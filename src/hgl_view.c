/*
 * BUILD (recovered in session 24, after the session-23 source was lost):
 *
 *   i686-w64-mingw32-gcc -O2 -s -shared -Wl,--kill-at -o HGL_VIEW.DLL \
 *       hgl_view.c -static-libgcc \
 *       -lgdi32 -luser32 -ld3d11 -ld3dcompiler -ldxguid -lole32 -lwinmm
 *
 *   mingw-w64 gcc 13 (win32 threads). Two things are not optional:
 *
 *   -Wl,--kill-at   The game looks the two entry points up BY NAME, as
 *                   "hFunc" and "hGetDLLName". Without this flag mingw
 *                   exports them decorated - "hFunc@8" - GetProcAddress
 *                   fails, and the game dies on "set display mode" with
 *                   nothing in any log to say why. Check it, do not assume:
 *                   objdump -p HGL_VIEW.DLL, the name pointer table must
 *                   read hFunc / hGetDLLName undecorated.
 *   -ldxguid        IID_ID3D11Texture2D lives there; without it the link
 *                   fails outright, which is at least honest.
 *
 *   Sanity check on the toolchain: this file with the session-24 edits
 *   backed out builds to exactly 155136 bytes, the size of the known good
 *   session-22 DLL. With them, 156160.
 */

/*
 * HGL_VIEW.DLL - a live 3D preview of Virtua Cop 2's geometry.
 *
 * The game keeps rendering normally: this DLL forwards every renderer call to
 * HGL_D3D.DLL untouched. On the way past, it copies the quads it sees, turns
 * their screen coordinates back into 3D using the projection recovered from
 * PPJ2DD.EXE, and draws them in a second window with a camera you can rotate.
 *
 * If the scene in that window turns like a real 3D scene, the reconstruction is
 * correct and the same geometry can go to a headset. If it does not, nothing in
 * the game is broken and the fix is local.
 *
 * Recovered projection (see vc2_projection.py for where each constant lives):
 *
 *      Z = (w mod 0x40000) / 8            view-space depth
 *      P =  w div 0x40000                 priority layer, not depth
 *      X = (x - 320) * Z / fx             fx = 320 / tan(fov/2)
 *      Y = (y - 240) * Z / fy             fy = 1.125 * fx
 *
 * Controls in the preview window:
 *      mouse drag      look around
 *      W A S D         move
 *      R               back to the game's own viewpoint
 *      F               wireframe on/off
 *
 * HGL_VIEW.ini, section [view]:
 *      target = HGL_D3D.DLL    backend to forward to
 *      fov    = 60             the game's field of view in degrees
 *      width  = 1280           preview window size
 *      height = 720
 *      skip3  = 1              drop priority layer 3 (the flat painted skyline;
 *                              it is drawn close and would sit in the street)
 *      inject = 1              turn controller aim from the VR app into mouse
 *                              and key input for the game (0 = off,
 *                              2 = PostMessage only, for a game that ignores
 *                              the real cursor)
 *      screen = 1              capture the game window into shared memory so
 *                              the VR app can show menus on a floating screen
 *
 * Input injection: the VR app writes aim_x/aim_y (640x480 screen space) and
 * button bits into shared memory. A thread here moves the real cursor over the
 * game window and synthesises button and key events. It only does that while
 * the game window is in the foreground, and it releases everything the moment
 * the VR app stops updating - so a dead VR process cannot leave the mouse
 * button stuck down.
 */

#define COBJMACROS
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <stdlib.h>
#include <d3d11.h>
#include <d3dcompiler.h>
#include <math.h>
#include <stdio.h>
#include <intrin.h>
#include "vc2_share.h"

/* ------------------------------------------------------------ proxy plumbing */

#define MAX_SLOTS   64
#define THUNK_SIZE  32
#define SLOT_INIT    0      /* +0x00: (hInst, hWnd, bmpNames, info) */
#define SLOT_GETINFO 6      /* +0x18 */
#define SLOT_FLUSH   9      /* +0x24 */
#define SLOT_TEX    10      /* +0x28: texture upload, 6 args */
#define SLOT_QUAD   11      /* +0x2C */
#define SLOT_SPRITE 12      /* +0x30: screen sprites, 4 priorities */
#define SLOT_LIGHT  14      /* +0x38: global light, HGL_D3D 0x10005C80 */

#ifndef PW_RENDERFULLCONTENT
#define PW_RENDERFULLCONTENT 2  /* Win 8.1+: ask DWM for the composited image */
#endif

static HINSTANCE g_self;
static HMODULE   g_target;
static char      g_targetName[MAX_PATH] = "HGL_D3D.DLL";
static char      g_iniPath[MAX_PATH];
static DWORD (__stdcall *g_realFunc)(void **, const char *);
static DWORD (__stdcall *g_realName)(void *);
static void     *g_real[MAX_SLOTS];
static BYTE     *g_thunks;
static volatile LONG g_slotCalls[MAX_SLOTS];     /* live counters, thunked   */
static LONG          g_slotShown[MAX_SLOTS];     /* per-frame delta for title */
static LONG          g_slotPrev[MAX_SLOTS];
static volatile DWORD g_probeAt;                 /* [P]: dump at this tick   */

/* ---------------------------------------------------- self-calibrating map */
/*
 * The upload table does not carry the id -> texture rule in any form we have
 * managed to invert, but the game window shows every quad already painted
 * with the right texture. So the DLL watches: for each on-screen quad it
 * crops the captured window at the quad's rectangle, compares the colour
 * histogram against every atlas entry of that bank, and votes. A stable
 * winner becomes the mapping for that id. [C] toggles learning; the picture
 * visibly snaps into place as ids get resolved.
 */
#define LEARN_MAX 2560
#define VOTE_K    6
typedef struct { int reg; float score; } Vote;
static DWORD g_ord[4096];            /* ingest ordinal per reg, per base  */
static DWORD g_ordNext[5];       /* running ordinal per band          */
static DWORD g_saveAt;                  /* autosave timer */

typedef struct { DWORD id, base, ord; } LearnRec;
static LearnRec g_pending[LEARN_MAX];   /* loaded, waiting for the entry     */
static int g_pendingN;
static Vote  g_vote[LEARN_MAX][VOTE_K];
static int   g_voteN[LEARN_MAX];
static int   g_learn[LEARN_MAX];        /* -1 unknown, else index into g_reg */
static int   g_learnCount;
static volatile LONG g_calib;           /* [C] */
static float g_kFit[3] = { -1, -1, -1 };/* fitted light scale per channel    */
static LONG  g_kN;                      /* samples folded in                 */

/* per-frame quad rectangles for the calibrator, double-buffered like verts */
typedef struct { DWORD id; float x0, y0, x1, y1; float sh[3]; } QRect;
#define QRECT_MAX 900
static QRect g_qrBuild[QRECT_MAX], g_qrDraw[QRECT_MAX];
static int   g_qrBuildN, g_qrDrawN;

static void histOfPixels(const DWORD *px, int stride, int w, int h,
                         float *out)
{
    int x, y, i;
    float mean = 1.0f, inv;
    double acc = 0.0;
    int n = 0;
    for (i = 0; i < 64; i++) out[i] = 0.0f;
    for (y = 0; y < h; y += 2)
        for (x = 0; x < w; x += 2) {
            DWORD c = px[y * stride + x];
            acc += ((c >> 16) & 255) + ((c >> 8) & 255) + (c & 255);
            n++;
        }
    if (!n) return;
    mean = (float)(acc / (n * 3));
    if (mean < 8.0f) mean = 8.0f;
    inv = 42.5f / mean;                  /* scale so the mean sits mid-range */
    for (y = 0; y < h; y += 2)
        for (x = 0; x < w; x += 2) {
            DWORD c = px[y * stride + x];
            int r = (int)(((c >> 16) & 255) * inv); if (r > 255) r = 255;
            int g = (int)(((c >> 8)  & 255) * inv); if (g > 255) g = 255;
            int b = (int)(( c        & 255) * inv); if (b > 255) b = 255;
            out[(r >> 6) * 16 + (g >> 6) * 4 + (b >> 6)] += 1.0f;
        }
    for (i = 0; i < 64; i++) out[i] /= (float)n;
}

static float histDist(const float *a, const float *b)
{
    int i;
    float d = 0.0f;
    for (i = 0; i < 64; i++) {
        float s = a[i] + b[i];
        float df = a[i] - b[i];
        if (s > 1e-6f) d += df * df / s;
    }
    return d;
}

/* what texture uploads told us: one line per call */
typedef struct { DWORD base, count, d1min, d1max; } TexCall;
static TexCall g_texCalls[32];
static int     g_texCallN;

#define PROBE_MAX 1024
static DWORD g_probeId[PROBE_MAX];
static LONG  g_probeCnt[PROBE_MAX];
static int   g_probeN;

/* ------------------------------------------------------------------ geometry */

#define MAX_QUADS 40000
static int g_quadBlend;                  /* blend mode of the quad in flight */
#define ADD_MAX (2048 * 6)

typedef struct { float x, y, z; DWORD col; float u, v; float d; } Vtx;

static Vtx      g_build[MAX_QUADS * 6];   /* two triangles per quad */
static Vtx      g_buildAdd[ADD_MAX];      /* translucent tail, drawn last */
static UINT     g_buildAddN;
#define L3_MAX (4096 * 6)
static Vtx      g_buildL3[L3_MAX];        /* kept for layout, no longer used */
static UINT     g_buildL3N;
static UINT     g_l3End, g_drawL3End;
static unsigned __int64 g_quadKey[MAX_QUADS]; /* sort key of each pushed quad */
/* Flat overlay - the drum, lives, CREDITS, our own HUD - is pinned to the
 * UNZOOMED focal length in the DLL, so it is the one thing in the buffer that
 * must not follow the camera when the game zooms. Mark it here, sort it to the
 * very tail, and tell the VR side where that tail starts: it can then draw
 * those quads through a second, unzoomed matrix and the HUD stays put while
 * the world magnifies. */
static unsigned char g_quadFlat[MAX_QUADS];
static unsigned char g_quadLayerB[MAX_QUADS];   /* engine sort layer, for feetfill */
static UINT     g_ovStart;                    /* first flat-overlay vertex */
static unsigned __int64 g_sortKey[MAX_QUADS];
static UINT     g_quadKeyN;

static int __cdecl cmp64(const void *a, const void *b)
{
    unsigned __int64 x = *(const unsigned __int64 *)a;
    unsigned __int64 y = *(const unsigned __int64 *)b;
    return (x > y) - (x < y);
}
static UINT     g_addStart;               /* first translucent vertex */
static UINT     g_drawAddStart;
static UINT     g_buildCount;
static Vtx      g_draw[MAX_QUADS * 6];
static UINT     g_drawCount;
static CRITICAL_SECTION g_lock;
static BOOL     g_ready;

static float    g_fx = 554.3f, g_fy = 623.6f;
static float    g_cx = 320.0f, g_cy = 240.0f;
static float    g_fxIni = 554.3f, g_fyIni = 623.6f;
static int      g_liveProj = 1;         /* take the projection from the game  */
static int      g_projOk;               /* the four globals were readable     */
static float    g_projFov;              /* current field of view, degrees     */
static float    g_fovDeg = 60.0f;
/* 644 came from "the camera sits 1030 units over the road" divided by a 1.6 m
 * eye height. That 1030 was later measured properly and turned out to be 215 -
 * the ini says so in the groundy comment - and nobody came back for this line.
 * So every distance in the world has been coming out 4.8 times too short: the
 * player's eye was 33 cm off the tarmac, a street was three metres wide, and
 * the whole city read as a model railway. It is the same arithmetic, with the
 * corrected number: 215 / 1.60 = 134. */
static float    g_unitsPerMetre = 134.0f;   /* eye 215 units over the road */
static HANDLE   g_shareMap;
static Vc2Frame *g_share;
static int      g_doShare = 1, g_doWindow = 1;
static int      g_skip3 = 1;
static int      g_winW = 1280, g_winH = 720;
static int      g_doInject = 1;         /* 0 off, 1 real input, 2 PostMessage */
static int      g_doScreen = 1;
static int      g_doShade  = 1;         /* 0 off, 1 luminance, 2 per-channel  */
static int      g_doTexdump = 0;        /* dump slot +0x28 calls to texdump\ */
static int      g_doTex    = 1;         /* decode textures into the atlas     */
static int      g_texMap   = 1;         /* 1: id = base+slot, 2: id = base+order */
static int      g_alphaKey = 1;         /* palette index 0 = transparent      */
static volatile LONG g_zflip = 0;       /* [Z]: flip the depth comparison */
static volatile LONG g_uvOrder = -1;    /* -1 = engine rule, 0..2 forced [T]  */
static volatile LONG g_texGain = 100;   /* percent; [G] cycles 25..400        */
static int      g_depthTest = 0;
static int      g_doSprites = 1;        /* draw the 2D sprite overlay slot  */
static float    g_sprDist = 312.0f;     /* how far the overlay hangs        */
static float    g_sprFar  = 90000.0f;   /* and how far the sky sits behind  */

/* the game's own crosshair, read live from its priority-0 sprites (640x480).
 * There is more than one prio-0 sprite in real gameplay (a static HUD reticle,
 * a leftover 2nd sight), so we keep a short ring of recent centres and, in the
 * hook, lock onto the one that is actually the moving gun crosshair. */
#define XHAIR_CAND 32
static volatile float g_candX[XHAIR_CAND], g_candY[XHAIR_CAND];
static volatile DWORD g_candT[XHAIR_CAND];
static volatile DWORD g_candTex[XHAIR_CAND];   /* texture id, for the log */
static volatile LONG  g_candW = 0;
static float          g_xhairEst = 320.0f, g_xhairEstY = 240.0f;  /* tracked lock, gun 0 */
static float          g_xhairEst2 = 320.0f, g_xhairEstY2 = 240.0f; /* tracked lock, gun 1 */
static volatile float g_xhairX = 320.0f, g_xhairY = 240.0f;       /* selected, for log */
static volatile LONG  g_xhairHits = 0;
static float          g_joyGain = 2.0f;
static int            g_joyMode = 1;
static int            g_joyLog  = 0;
static int      g_skyDome = 1;          /* wrap the backdrop around the head */
static int      g_skySeg  = 12;         /* segments per tile                 */
static int      g_skyRep  = 2;          /* copies left and right             */
typedef struct { DWORD tex; float x0, y0, x1, y1, sh[3]; } SkyTile;
static DWORD    g_skyTex[16];           /* textures known to be backdrop */
static int      g_skyTexN;
static float    g_skySpan;
static float    g_skySpanA;             /* widest panorama ever seen, radians */
static int      g_skyRing;              /* tiles round the panorama, 0 = unknown */
/* what the dome actually did last frame. ring/locked/fail say the panorama was
 * understood; they do NOT say that a single triangle was written. These do. */
static UINT     g_domeQ;                /* quads the dome emitted             */
static int      g_domeSkip;             /* ring steps dropped for no texture  */
static DWORD    g_domeWalk[2];          /* the ids the chain walked to        */
static int      g_skyDebug;             /* [view] skydebug: flat band, no tex */
/* The game blits the panorama only in frames where its own camera can see it.
 * Aim that camera at a wall of windows and no backdrop is drawn at all - on a
 * flat screen nobody notices, because the wall fills the frame. In a headset
 * the head looks past the wall and finds the clear colour. The dome does not
 * need the blit: the ring is already learnt and it is nailed to the world
 * matrix, so keep drawing it from what is known, exactly as the city geometry
 * is kept. skyhold is how many frames it survives without being re-seen. */
static int      g_skyHold = 600;        /* [view] skyhold, frames, 0 = off    */
static int      g_skyHoldOk;            /* the remembered state is usable     */
static float    g_skyHoldSh[3];         /* shading of the last real sky frame */
static int      g_skyMiss;              /* frames since the game last blitted */
static int      g_skyHeld;              /* this frame was drawn from memory   */
/* Once the ring is known the panorama is a fixed object in the world, and the
 * only honest place to get its bearing is the view matrix - not the screen.
 * Locked once: which texture is tile 0, the world bearing of its left edge,
 * and the tangents of its top and bottom edges. After that the dome is built
 * from the matrix alone and nothing the game does to the sprite - scrolling,
 * clipping it at the screen edge, rescaling it on a zoom - can move it. */
static int      g_skyLocked;            /* [view] skylock effective */
static DWORD    g_skyLockTex;
static float    g_skyPhase;             /* world bearing of tile 0's left edge */
static float    g_skyTanT, g_skyTanB;   /* tan(elevation) of its top and bottom */
static int      g_skyLock = 1;          /* [view] skylock */
static int      g_skyRingDraw = 8;       /* tiles to lay round the dome: taken
                                          * from the tile's measured angular
                                          * width, not the successor chain, so a
                                          * scrolling panorama that cross-links
                                          * its two visible tiles into a bogus
                                          * 2-cycle cannot stretch each tile to
                                          * 180 degrees across half the sky */
/* which panorama tile follows which, learned from tiles that arrive edge to
 * edge. Enough to walk the whole ring from any single tile still on screen. */
static DWORD g_succA[16], g_succB[16];
static int   g_succN;

static void skyLink(DWORD a, DWORD b)
{
    int i;
    if (a == b) return;
    for (i = 0; i < g_succN; i++)
        if (g_succA[i] == a) { g_succB[i] = b; return; }
    if (g_succN >= 16) return;
    g_succA[g_succN] = a;
    g_succB[g_succN] = b;
    g_succN++;
}

/* step n places around the ring from tex, forwards or backwards */
/* How many tiles go round. The successor chain is learned from tiles arriving
 * edge to edge; when it closes on itself, that cycle IS the panorama, and the
 * tile's angular width is exactly 360/N - a constant, not something to measure
 * off the screen. Returns 0 while the ring is still open. */
static int skyRingLen(DWORD tex)
{
    DWORD cur = tex;
    int n, i;
    for (n = 1; n <= 16; n++) {
        int hit = -1;
        for (i = 0; i < g_succN; i++) if (g_succA[i] == cur) { hit = i; break; }
        if (hit < 0) return 0;                  /* chain runs out: not a ring */
        cur = g_succB[hit];
        if (cur == tex) return n;
    }
    return 0;
}

/* how many steps forward from a to b round the ring, or -1 */
static int skyIndexOf(DWORD a, DWORD b, int ring)
{
    DWORD cur = a;
    int n, i;
    for (n = 0; n < ring; n++) {
        int hit = -1;
        if (cur == b) return n;
        for (i = 0; i < g_succN; i++) if (g_succA[i] == cur) { hit = i; break; }
        if (hit < 0) return -1;
        cur = g_succB[hit];
    }
    return -1;
}

static DWORD skyWalk(DWORD tex, int n)
{
    int guard = 0;
    while (n > 0 && guard++ < 64) {
        int i, hit = -1;
        for (i = 0; i < g_succN; i++) if (g_succA[i] == tex) { hit = i; break; }
        if (hit < 0) return tex;            /* ring unknown: repeat this tile */
        tex = g_succB[hit];
        n--;
    }
    while (n < 0 && guard++ < 64) {
        int i, hit = -1;
        for (i = 0; i < g_succN; i++) if (g_succB[i] == tex) { hit = i; break; }
        if (hit < 0) return tex;
        tex = g_succA[hit];
        n++;
    }
    return tex;
}

static int      g_skyCap = 1;           /* close the dome overhead           */
static float    g_capY;
static DWORD    g_capCol;
static int      g_capHave;

static int skyTexKnown(DWORD tex)
{
    int i;
    for (i = 0; i < g_skyTexN; i++) if (g_skyTex[i] == tex) return 1;
    return 0;
}
static void skyTexRemember(DWORD tex)
{
    if (skyTexKnown(tex) || g_skyTexN >= 16) return;
    g_skyTex[g_skyTexN++] = tex;
}
static SkyTile  g_sky[8];
static int      g_skyN;
static float    g_sxMin, g_sxMax;       /* how wide the game submits at all  */
static float    g_syMin, g_syMax;
static float    g_syMinS, g_syMaxS;
static int      g_noCull = 1;           /* patch the game's frustum reject   */
static int      g_cullPatched;
static volatile LONG g_cullState;   /* 0 off, 1 patched, 2 not found, 3 denied */
static DWORD    g_cullAt, g_cullBase, g_cullSpan;
static int      g_cullFound;
static int      g_noObjCull = 1;        /* patch the per-object angle reject */
static int      g_ocullPatched;
static volatile LONG g_ocullState;  /* 0 off, 1 patched, 2 not found, 3 denied */
static DWORD    g_ocullAt;
static int      g_ocullFound;
static float    g_sxMinS, g_sxMaxS;
static DWORD    g_quadFrom[8];          /* return addresses of the submitter */
/* PPJ2DD.EXE 0x004CF22C holds a pointer to the 3x4 matrix the vertex
 * transform at 0x00442430 is using right now: three basis vectors at +0x00,
 * +0x0C, +0x18 and the translation at +0x24. It is still valid when the quad
 * reaches us, so every quad can be tagged with the transform it came from.
 * If the scenery all shares one matrix, that matrix IS the camera, and the
 * whole city can be unprojected into world space and kept. */
#define MTX_PTR_RVA 0x000CF22C
typedef struct { float m[12]; int n; } MtxSeen;
static MtxSeen  g_mtx[12];
static int      g_mtxN;
static MtxSeen  g_mtxDump[12];
static int      g_mtxDumpN;
static int      g_mtxTotal, g_mtxTotalS;
static int      g_quadFromN;
typedef struct { DWORD tex; int prio; float x0, y0, x1, y1; } SprInfo;
static SprInfo  g_sprInfo[32];
static int      g_sprN2, g_sprShownN;
static SprInfo  g_sprDump[32];
static DWORD    g_dropDyn, g_dropVar;   /* quads dropped, per reason        */        /* the engine has no z-buffer at all  */
static int      g_amb[3];               /* global light, slot +0x38           */
static int      g_skyAmb;               /* [view] skyamb: light the sky dome   */
static int      g_splashDepth = 1;      /* [view] splashdepth: hit sprites on the wall */
static DWORD    g_splashHits;
static DWORD    g_shotTex = 1344;       /* [view] shottex: the game's shot/hit flash sprite */
static int      g_shotSpr = 1;          /* [view] shotspr: 0 hide it, 1 place on surface */
/* [probe] hit-splash placement: where the ray went */
static DWORD    g_spTry, g_spHit, g_spMiss, g_spNoWorld;
/* Sprites the ray cast could not put on a surface end up at sprdist - 2.3 m
 * from the eye. That is right for a muzzle flash and catastrophic for a piece
 * of distant scenery: the two eyes then see it a hand's width apart while it
 * is drawn a street away. Count what is being hung there, and remember the
 * biggest one, so a "wrong depth" report has a texture number in it. */
/* HOW FAR AWAY IS WHAT WE DRAW. Geometry that slides when the head moves is
 * geometry that is nearer than it looks: parallax goes as one over distance,
 * so a building three hundred metres off cannot move, and one that moves is
 * not three hundred metres off. Measure it - per layer, how many quads and
 * the nearest and furthest in metres, plus the single biggest quad in the
 * frame with its texture and its distance. If a skyline turns out to sit at
 * ten metres then the GAME put it there, and no amount of exactness in the
 * reconstruction will move it; that is a different repair. */
typedef struct { DWORD n; float dmin, dmax; } LayerDist;
static LayerDist g_ld[16], g_ldS[16];
static LayerDist g_ld0[16], g_ld0S[16];  /* engine's own pass only, for the backdrop rule */
static float     g_bigArea, g_bigAreaS, g_bigDist, g_bigDistS;
static float     g_wideSr, g_wideSrS, g_wideDist, g_wideDistS, g_wideArea, g_wideAreaS;
static DWORD     g_wideTex, g_wideTexS;
static DWORD     g_bigTex, g_bigTexS;
/* Paint every surface by how far away we put it, so "that building is at the
 * wrong depth" becomes a thing you can read off the picture instead of a
 * thing we argue about. Red is under 10 m, orange 25, yellow 50, green 100,
 * cyan 200, blue beyond. A building that looks a street away and comes out
 * red is being drawn too close; one that comes out blue is where it should
 * be and the trouble is elsewhere. */
static int      g_distDebug;            /* [view] distdebug */
static int      g_aimProbe;             /* [view] aimprobe */
static DWORD cfgNum(const char *key, DWORD def);   /* defined with the rest of the ini reader */
static int   cfgInt(const char *key, int def);
static int      g_nwRadial = 1;         /* [view] nwradial: radial keys for the nonworld quads too */
static DWORD    g_farLayers;            /* [view] farlayers: bitmask of sort layers to push out */
static int      g_farAuto = 1;          /* [view] farlayerauto: push a sparse far layer automatically */
static int      g_farAutoCount = 40;    /* [view] farautocount: at most this many quads to count as a backdrop */
static int      g_farAutoNear = 12;     /* [view] farautonear: nearest quad must be past this, metres */
static int      g_farScale = 800;       /* [view] farscale: how far, in percent */

/* ------------------------------------------------------------- aim probe
 * "A building across the street is drawn at arm's length" cannot be chased
 * with a colour ramp: the ramp says WHICH BAND, never WHICH QUAD, and the
 * answer that matters is what the engine itself said about that quad. So
 * let the player point at it. The laser already lands on a 640x480 point
 * (the light gun's own aim, in shared memory); on the frame after a shot
 * every quad whose screen box holds that point is written out with
 * everything that decided its depth:
 *
 *   the engine's own w per corner  - layer * 0x40000 + z * 8, so the metres
 *                                    the ENGINE thinks the corner is at
 *   our reconstructed distance     - what we put it at
 *   true<n>                        - how many corners came from the
 *                                    projector hook rather than an unproject
 *   world / pass / NONWORLD        - which submission path it arrived by
 *
 * If the engine's z and ours agree, the game really is drawing a small model
 * close by and no reconstruction can fix it. If they disagree, the bug is
 * ours and the line says which corner. One shot, one fact. */
#define AIM_MAX 24
typedef struct {
    DWORD tex, flags, ra, w[4];
    int   layer, trueN, path, x0, y0, x1, y1;
    float dm, zm[4];
} AimRec;
static AimRec       g_aim[AIM_MAX];
static volatile LONG g_aimN;
static volatile LONG g_aimArm;
static DWORD        g_aimLast;
static int      g_sprMissFar = 96;      /* [view] sprmissfar, screen points */
static DWORD    g_bigMiss, g_bigMissS;
static DWORD    g_farSpr, g_farSprS, g_farSprTex, g_farSprTexS;
static float    g_farSprW, g_farSprH, g_farSprWS, g_farSprHS;
static struct { DWORD tex; int prio, base; UINT nb, ntri; float t, mx, my; } g_spS[8];
static volatile LONG g_spSW;
static DWORD g_skS; static struct { DWORD tex; float x0,y0,x1,y1; int sh; } g_skR[8]; static volatile LONG g_skW;
static DWORD g_bqS; static struct { DWORD id, w, col; int x0,y0,x1,y1; } g_bqR[8]; static volatile LONG g_bqW;
static DWORD g_nnS, g_nnSeen[4096]; static struct { DWORD id, w, ra; int cx, cy, wd, ht, dt, xx, xy; } g_nnR[16];
static volatile DWORD g_fireTick; static DWORD g_fireWas; static volatile LONG g_nnW;
static DWORD g_naS; static struct { DWORD id, w; int kind, prio, cx, cy, wd, ht, dt, ax, ay, inw; } g_naR[16]; static volatile LONG g_naW;
static void nearAim(DWORD id, DWORD w, int kind, int prio, float x0, float y0, float x1, float y1, int inw)
{
    DWORD now = GetTickCount(); int ax, ay; float cx, cy;
    if (!g_share || now - g_fireTick > 300) return;
    ax = (int)g_share->aim_x; ay = (int)g_share->aim_y;
    cx = (x0 + x1) * 0.5f; cy = (y0 + y1) * 0.5f;
    if (cx - ax > 120 || ax - cx > 120 || cy - ay > 120 || ay - cy > 120) return;
    {
        LONG k = (InterlockedIncrement(&g_naW) - 1) % 16;
        g_naS++; g_naR[k].id = id; g_naR[k].w = w; g_naR[k].kind = kind; g_naR[k].prio = prio;
        g_naR[k].cx = (int)cx; g_naR[k].cy = (int)cy; g_naR[k].wd = (int)(x1 - x0); g_naR[k].ht = (int)(y1 - y0);
        g_naR[k].dt = (int)(now - g_fireTick); g_naR[k].ax = ax; g_naR[k].ay = ay; g_naR[k].inw = inw;
    }
}
static DWORD g_ssS; static struct { DWORD tex; int prio; int x0,y0,x1,y1; } g_ssR[12]; static volatile LONG g_ssW;
static DWORD    g_prevKey;              /* sort key of the previous quad      */
static volatile LONG g_sprN[4];         /* sprite calls per priority          */
static LONG     g_sprShown[4], g_sprPrev[4];
static volatile LONG g_alphaMode;       /* [K]: 0 engine, 1 solid, 2 all */
static volatile LONG g_neutral;         /* [U]: draw textures unshaded        */
static volatile LONG g_showAtlas;       /* [A]: fullscreen view of the atlas  */
static DWORD g_idHitMin = ~0u, g_idHitMax, g_idMissMin = ~0u, g_idMissMax;
static DWORD g_idHitMinS = ~0u, g_idHitMaxS, g_idMissMinS = ~0u, g_idMissMaxS;
static int      g_capture  = 2;         /* 1 PrintWindow, 2 copy from screen  */

/* ------------------------------------------------------------- texture atlas */
/*
 * Slot +0x28 uploads decoded straight into a BGRA sheet. Table entry:
 * dword0 = height<<16 | width, pixels 8-bit palettised, packed tight in table
 * order; the call's palette is 256 x 0x00RRGGBB. arg3 of the call is the base
 * of this bank in the game's global texture numbering and entry dword1 is the
 * slot offset from that base - quad.texture should equal base + slot.
 * That last equation is the one thing not yet confirmed on a live run, hence
 * texmap in the ini and [T] in the preview window for the corner order.
 */

#define REG_MAX 4096
#define BAND_MAX 5

typedef struct {
    DWORD key; DWORD base;
    float u0, v0, u1, v1;
    int used;
    DWORD d3;                           /* table entry dword3: bit1 colour key,
                                         * bit2 dynamic (engine skips in quads) */
    float hist[64];                     /* mean-normalised 4x4x4 colour hist */
    float mean[3];                      /* average R,G,B of opaque texels    */
    float top[3];                       /* average of the top rows only      */
} TexReg;
static TexReg g_reg[REG_MAX];
static int    g_regCount;
static DWORD *g_atlas;                            /* VC2_ATLAS_W x H BGRA */
static int    g_atlasDirty;
static volatile LONG g_pvAtlDirty;      /* preview copy of the atlas is stale */

/* the game treats textures as slot memory: an upload call fills slots
 * [base .. base+count) in order, later uploads overwrite earlier ones, and
 * quad.texture = base + index (confirmed against live probe data on four
 * stages). Each base gets its own horizontal band of the atlas; when a band
 * overflows, its cursor resets - slots that were still pointing into the old
 * generation go stale until their next upload, which in practice is the next
 * scene load for that very base. */
typedef struct { DWORD base; int y0, rows, curX, curY, shelfH; int live; } TexBand;
static TexBand g_band[BAND_MAX] = {
    {    0,    0, 1024, 0, 0, 0, 1 },    /* system: loaded once at boot */
    { 1600, 1024, 1536, 0, 0, 0, 1 },    /* stage bank, biggest churn   */
    { 1900, 2560,  768, 0, 0, 0, 1 },
    { 2000, 3328,  512, 0, 0, 0, 1 },
    {    0, 3840,  256, 0, 0, 0, 0 },    /* spare for a base we have not met */
};

static TexBand *bandFor(DWORD base)
{
    int i;
    for (i = 0; i < BAND_MAX; i++)
        if (g_band[i].live && g_band[i].base == base) return &g_band[i];
    for (i = 0; i < BAND_MAX; i++)
        if (!g_band[i].live) { g_band[i].live = 1; g_band[i].base = base; return &g_band[i]; }
    return NULL;
}

/* the band overflowed: repack every live slot tightly instead of dropping
 * them. Bank 0 and the resident top of the boot upload never come again, so
 * a plain reset would lose them for good; compaction never loses anything as
 * long as the live pixels genuinely fit. */
static void bandCompact(TexBand *b)
{
    static DWORD *tmp;                  /* one band worth of scratch */
    int i, cx = 0, cy = 0, sh = 0;
    if (!tmp)
        tmp = (DWORD *)VirtualAlloc(NULL,
                  (SIZE_T)VC2_ATLAS_W * VC2_ATLAS_H / 2 * 4,
                  MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    if (!tmp) {                          /* no memory: fall back to reset */
        b->curX = b->curY = b->shelfH = 0;
        for (i = 0; i < g_regCount; i++)
            if (g_reg[i].used && g_reg[i].base == b->base) g_reg[i].used = 0;
        return;
    }
    for (i = 0; i < g_regCount; i++) {
        TexReg *r = &g_reg[i];
        int w, h, ox, oy, y;
        if (!r->used || r->base != b->base) continue;
        ox = (int)(r->u0 * VC2_ATLAS_W - 0.5f + 0.5f);   /* undo the inset */
        oy = (int)(r->v0 * VC2_ATLAS_H - 0.5f + 0.5f);
        w  = (int)((r->u1 - r->u0) * VC2_ATLAS_W + 1.0f + 0.5f);
        h  = (int)((r->v1 - r->v0) * VC2_ATLAS_H + 1.0f + 0.5f);
        if (cx + w > VC2_ATLAS_W) { cy += sh; cx = 0; sh = 0; }
        if (cy + h > b->rows) { r->used = 0; continue; }  /* truly out of room */
        for (y = 0; y < h; y++)
            CopyMemory(tmp + (SIZE_T)(cy + y) * VC2_ATLAS_W + cx,
                       g_atlas + (SIZE_T)(oy + y) * VC2_ATLAS_W + ox,
                       (SIZE_T)w * 4);
        r->u0 = ((float)cx + 0.5f) / VC2_ATLAS_W;
        r->v0 = ((float)(b->y0 + cy) + 0.5f) / VC2_ATLAS_H;
        r->u1 = ((float)(cx + w) - 0.5f) / VC2_ATLAS_W;
        r->v1 = ((float)(b->y0 + cy + h) - 0.5f) / VC2_ATLAS_H;
        cx += w;
        if (h > sh) sh = h;
    }
    for (i = 0; i < b->rows; i++)
        CopyMemory(g_atlas + (SIZE_T)(b->y0 + i) * VC2_ATLAS_W,
                   tmp + (SIZE_T)i * VC2_ATLAS_W, VC2_ATLAS_W * 4);
    b->curY = cy + sh;
    b->curX = 0;
    b->shelfH = 0;
    g_atlasDirty = 1;
    InterlockedExchange(&g_pvAtlDirty, 1);
}

static int atlasAlloc(TexBand *b, int w, int h, int *ox, int *oy)
{
    if (w > VC2_ATLAS_W || h > b->rows) return 0;
    if (b->curX + w > VC2_ATLAS_W) {
        b->curY += b->shelfH;
        b->curX = 0;
        b->shelfH = 0;
    }
    if (b->curY + h > b->rows) {
        bandCompact(b);
        if (b->curX + w > VC2_ATLAS_W) { b->curY += b->shelfH; b->curX = 0; b->shelfH = 0; }
        if (b->curY + h > b->rows) return 0;
    }
    *ox = b->curX;
    *oy = b->y0 + b->curY;
    b->curX += w;
    if (h > b->shelfH) b->shelfH = h;
    return 1;
}

static TexReg *regSlot(DWORD key)
{
    int i, freeI = -1;
    for (i = g_regCount - 1; i >= 0; i--) {
        if (g_reg[i].used && g_reg[i].key == key) return &g_reg[i];
        if (!g_reg[i].used && freeI < 0) freeI = i;
    }
    if (freeI >= 0) return &g_reg[freeI];
    if (g_regCount < REG_MAX) return &g_reg[g_regCount++];
    return NULL;
}

static const TexReg *regFind(DWORD id)
{
    int i;
    for (i = g_regCount - 1; i >= 0; i--)
        if (g_reg[i].used && g_reg[i].key == id)
            return &g_reg[i];
    return NULL;
}
static HWND     g_gameWnd;              /* the game's own window, from slot 0 */

#define LAYER 0x40000

/* --------------------------------------------------------- live projection
 * PPJ2DD projects a vertex at 0x00445BE0, and it does exactly this:
 *
 *   sx = word[0x004CF80A] + view.x * [0x004CF23C] / view.z
 *   sy = word[0x004CF808] + view.y * [0x004CF238] / view.z
 *
 * with 0x004CF23C = halfWidth / tan(fov/2) and 0x004CF238 = 1.5 * halfHeight
 * / tan(fov/2), both rebuilt by 0x00442090 from the field of view angle in
 * word 0x004DB8A4 - which the game CHANGES AT RUNTIME. 0x0043D6F0 is the zoom:
 * it walks 0x004DB8A4 down by 0x91 per step from 0x2AAA (60 degrees, which is
 * where the ini value of 60 came from) as far as 0x0CCC, about 18 degrees.
 *
 * So a fixed fx is right only while the game is not zoomed. At full zoom it
 * is off by a factor of three and a bit, and since every quad is unprojected
 * with it, the whole scene inflates and tears - which is exactly what the
 * zoomed screenshots show. Read the four values the game is using right now
 * instead of assuming them, and the unprojection is correct by construction
 * at every zoom step, no calibration and no table of modes. */
#define PROJ_FX_RVA  0x000CF23C
#define PROJ_FY_RVA  0x000CF238
#define PROJ_CX_RVA  0x000CF80A
#define PROJ_CY_RVA  0x000CF808

static void wcReset(void);
static int  g_wcOn;

static void readProjection(void)
{
    static const float *pfx, *pfy;
    static const short *pcx, *pcy;
    static int tried;
    float fx, fy;

    if (!g_liveProj) return;
    if (!tried) {
        BYTE *base = (BYTE *)GetModuleHandleA(NULL);
        tried = 1;
        if (!base) return;
        if (IsBadReadPtr(base + PROJ_FX_RVA, 4) ||
            IsBadReadPtr(base + PROJ_FY_RVA, 4) ||
            IsBadReadPtr(base + PROJ_CX_RVA, 2) ||
            IsBadReadPtr(base + PROJ_CY_RVA, 2)) return;
        pfx = (const float *)(base + PROJ_FX_RVA);
        pfy = (const float *)(base + PROJ_FY_RVA);
        pcx = (const short *)(base + PROJ_CX_RVA);
        pcy = (const short *)(base + PROJ_CY_RVA);
    }
    if (!pfx) return;
    fx = *pfx; fy = *pfy;
    /* nonsense means the game has not set them up yet - keep what we have */
    if (!(fx > 10.0f && fx < 200000.0f) || !(fy > 10.0f && fy < 200000.0f)) return;
    if (*pcx < 1 || *pcx > 4096 || *pcy < 1 || *pcy > 4096) return;
    if (g_fx != fx) {
        /* the cache holds world points built with the old focal length, and
         * they are simply wrong now - keeping them is how the zoom scenes get
         * their torn geometry */
        if (g_projOk && g_wcOn) wcReset();
        g_projFov = (float)(2.0 * atan(320.0 / fx) * 180.0 / 3.14159265358979);
    }
    g_fx = fx; g_fy = fy;
    g_cx = (float)*pcx; g_cy = (float)*pcy;
    g_projOk = 1;
}

static void unproject(float sx, float sy, DWORD w, float *ox, float *oy, float *oz)
{
    DWORD layer = w / LAYER;
    float z = (float)(w - layer * LAYER) / 8.0f;
    *ox =  (sx - g_cx) * z / g_fx;
    *oy = -(sy - g_cy) * z / g_fy;     /* screen y grows downwards, world y up */
    *oz = -z;                          /* OpenXR convention: forward is -Z */
}

/* ------------------------------------------------- true view-space vertices
 *
 * Everything above turns a SCREEN quad back into 3D. That works, and it can
 * only ever recover what the screen could hold - and the screen is a sixty
 * degree window. A vertex behind the eye has no screen position at all.
 *
 * PPJ2DD projects at 0x00445BE0 and its first act is
 *
 *      fld [ebx+8] ; fcomp [0x004CF800] ; jbe -> write zeros
 *
 * so a vertex nearer than the near plane leaves with sx = cx, sy = cy, w = 0.
 * 0x00442560 then drops the whole polygon, four times over:
 *
 *      mov edx,[eax+ecx+0x0C] ; test edx,edx ; jle <next polygon>
 *        at 0x004425A7, 0x004425BC, 0x004425D1, 0x004425E6
 *
 * THAT is why there is nothing behind you. Not the frustum test - that is
 * already stubbed. Not the object test - already stubbed. Not the streaming -
 * the objects behind you belong to the chunk you are standing in and 0x440C00
 * walks all of them. The geometry is in memory, the objects are walked, the
 * vertices are transformed, and then the projection deletes them.
 *
 * No unprojection can undo that; there is no screen position to undo. But one
 * step earlier the engine has exactly what is wanted: 0x00442430 (and the same
 * loop inlined at 0x00443CFF) writes the VIEW SPACE x,y,z of every vertex into
 * an array and hands that array to 0x00445BE0 as arg1. Hook that one function
 * and every vertex the engine transforms - in front of the eye or behind it -
 * arrives as three honest floats.
 *
 * Getting them back onto the right quad needs no bookkeeping either. The quad
 * that turns up at slot +0x2C carries a bit-exact 16 byte COPY of the
 * projected record (0x00442623, four dword moves), so the record is its own
 * key: remember {sx,sy,extra,w} -> {x,y,z} at projection time and look it up
 * when the quad arrives. Two vertices with the same key are the same point to
 * within an eighth of a unit, so a collision costs nothing.
 *
 * Except behind the eye, where every record is the same zeros and would
 * collide with every other. Those get stamped: sx is overwritten with a unique
 * bit pattern in [-4,-2), which is off screen, is never read on the way here
 * (0x00442500 is our stub, the clipper at 0x00442960 works from the view space
 * array, and HGL_D3D never sees these quads because wrap_quad holds them back
 * - w = 0 would be a divide by zero in its sz = K/w), and makes the key
 * unique again.
 *
 * Cost: one hash insert per transformed vertex, a few thousand a frame.
 *
 * NOT VERIFIED ON A LIVE RUN. truexyz defaults to 0. Everything below is
 * inert until it is switched on.
 */
static volatile LONG g_inClip;          /* inside the top-level clipper detour */
#define TX_BITS  18                     /* 262144 entries, 8 MB: six passes' worth of vertices */
#define TX_SIZE  (1 << TX_BITS)
#define TX_PROBE 16
typedef struct { DWORD k[4]; DWORD v[3]; DWORD gen; } TxEnt;
static TxEnt  *g_tx;
static DWORD   g_txGen = 1;
static DWORD   g_txTag;
static int     g_trueXyz;               /* [view] truexyz */
static int     g_behindOn;              /* [view] behind  */
static DWORD   g_txIns, g_txHit, g_txMiss, g_txBadHit, g_txBadHitS;
static DWORD   g_txInsS, g_txHitS, g_txMissS;
static DWORD   g_bentDrop, g_bentDropS;

/* ---- wedge probe: where does a raised corner of an asphalt quad come from ----
 * g_probeObj is the object omDraw is currently drawing (0 when the quad came
 * from somewhere else). When pushQuad reconstructs a quad with one corner high
 * in the sky and another near the ground - the wedge - it records, once every
 * two seconds, the texture, the drawing object, that object's OWN game-space
 * Y range, and the raised height. A flat asphalt object whose own vertices
 * span almost no Y but whose quad reaches +1800 proves the height is NOT the
 * object's - an alias; a genuinely tall object proves the opposite. */
static DWORD   g_probeObj;
static int     g_probeFlat;
static float   g_probeYlo, g_probeYhi;
static int     g_wedgeFix = 1;          /* [view] wedgefix: drop flat-object sky quads */
static int     g_wedgeHi = 600;         /* [view] wedgehi: flat-object ceiling, render units */
static DWORD   g_wedgeDrop, g_wedgeDropS;
static int     g_nearDropX = 1;         /* [view] neardropx: drop all-near-plane exact quads */
static DWORD   g_nearCardDrop, g_nearCardDropS;
static int     g_skyCull = 1;           /* [view] skycull: drop far high backdrop blades */
static int     g_skyHi = 3000;          /* [view] skyhi: game units up            */
static int     g_skyDist = 16000;       /* [view] skydist: game units out         */
static DWORD   g_skyCullN, g_skyCullNS;
static DWORD   g_wedgeTex, g_wedgeObj, g_wedgeSeen, g_wedgeSeenS;
static DWORD   g_wedgePass;
static float   g_wedgeObjYlo, g_wedgeObjYhi, g_wedgeRaise, g_wedgeLow;
static float   g_wedgeObjYloS, g_wedgeObjYhiS, g_wedgeRaiseS, g_wedgeLowS;
static DWORD   g_wedgeTexS, g_wedgeObjS, g_wedgePassS;
static DWORD   g_behindQ, g_behindQS, g_behindHeld;

/* The generation carries the PASS in its low three bits. The table is shared
 * by all six passes of a frame, and the record alone does not name a vertex
 * across them: beyond 32767 units the projector writes a CONSTANT w, so a
 * far vertex of the native pass and a far vertex of a rotated pass land on
 * the same {sx,sy,extra,w} systematically - measured live at the quay, sea
 * quads were picking up corners of the monorail deck, +1792 in y, exactly
 * one deck height, and the wedges fanned into the sky. A vertex is stored
 * and looked up strictly within its own pass now; a cross-pass hit is a
 * miss, which is what it always really was. */
static volatile LONG g_pass;            /* tentative; defined with the passes */

static DWORD txCurGen(void)
{
    return (g_txGen << 3) | ((DWORD)g_pass & 7u);
}

static DWORD txHash(const DWORD *k)
{
    DWORD h = k[0] * 0x9E3779B1u;
    h ^= k[1] + 0x85EBCA6Bu + (h << 6) + (h >> 2);
    h ^= k[2] + 0xC2B2AE35u + (h << 6) + (h >> 2);
    h ^= k[3] + 0x27D4EB2Fu + (h << 6) + (h >> 2);
    h ^= (DWORD)g_pass * 0x632BE5ABu;
    h ^= h >> 15;
    return h & (TX_SIZE - 1);
}

/* 0 inserted, 1 same key and same point (fine), 2 same key but ANOTHER point
 * (the record does not identify the vertex - see projThunk), 3 no room */
static DWORD   g_txBump, g_txFull, g_txBumpS, g_txFullS;
static int txPut(const DWORD *k, const DWORD *v)
{
    DWORD i = txHash(k), n;
    DWORD cg = txCurGen();
    for (n = 0; n < TX_PROBE; n++, i = (i + 1) & (TX_SIZE - 1)) {
        TxEnt *e = &g_tx[i];
        if ((e->gen >> 3) == g_txGen) {
            if (e->gen == cg &&
                e->k[0] == k[0] && e->k[1] == k[1] &&
                e->k[2] == k[2] && e->k[3] == k[3])
                return (e->v[0] == v[0] && e->v[1] == v[1] && e->v[2] == v[2]) ? 1 : 2;
            continue;
        }
        e->k[0] = k[0]; e->k[1] = k[1]; e->k[2] = k[2]; e->k[3] = k[3];
        e->v[0] = v[0]; e->v[1] = v[1]; e->v[2] = v[2];
        e->gen  = cg;
        g_txIns++;
        return 0;
    }
    g_txFull++;
    return 3;
}

static const DWORD *txGet(const DWORD *k)
{
    DWORD i, n;
    if (!g_tx) return NULL;
    i = txHash(k);
    {
        DWORD cg = txCurGen();
        for (n = 0; n < TX_PROBE; n++, i = (i + 1) & (TX_SIZE - 1)) {
            const TxEnt *e = &g_tx[i];
            if ((e->gen >> 3) != g_txGen) return NULL;
            if (e->gen == cg &&
                e->k[0] == k[0] && e->k[1] == k[1] &&
                e->k[2] == k[2] && e->k[3] == k[3]) return e->v;
        }
    }
    return NULL;
}

/* the engine's own projection, behind our detour */
static void (__cdecl *g_projOrig)(const void *v, void *out, DWORD layer);

static void __attribute__((force_align_arg_pointer)) __cdecl
projThunk(const void *v, void *out, DWORD layer)
{
    DWORD *o = (DWORD *)out;
    int r, n;
    g_projOrig(v, out, layer);
    if (!g_tx) return;
    /* inside the clipper detour the engine is projecting corners, midpoints
     * and centres of a polygon we are going to emit from its true corners
     * anyway. Nobody looks those up, and there are twelve of them per call. */
    if (g_inClip) return;
    if (o[3] == 0) {                    /* nearer than the near plane */
        o[0] = 0xC0000000u | ((g_txTag++) & 0x007FFFFFu);
        o[1] = 0;
    }
    /* Beyond 32767 units the projector writes a constant w and a constant
     * rhw (float(w) - 0x00445C3A stores the depth word into the rhw slot), so
     * every far vertex on one screen ray has the SAME record: the road's
     * vanishing point is hundreds of such vertices. Make the record unique by
     * nudging sx one ULP at a time - the engine reads the nudged copy, which
     * is a millionth of a pixel, and the key names one vertex again. */
    for (n = 0; n < 32; n++) {
        r = txPut(o, (const DWORD *)v);
        if (r != 2) break;
        o[0]++;
        g_txBump++;
    }
}

/* 0x00445BE0: sub esp,8 / push ebx / mov ebx,[esp+0x10] - eight bytes, no jump
 * lands inside them, so a plain five byte detour with the prologue relocated
 * into a trampoline is enough. */
#define PROJ_FUNC 0x00445BE0
static const BYTE PROJ_SIG[] = { 0x83,0xEC,0x08,0x53,0x8B,0x5C,0x24,0x10 };
static volatile LONG g_projState;   /* 0 off, 1 hooked, 2 not found, 3 denied */

static void installProjHook(BYTE *base)
{
    BYTE *p = base + (PROJ_FUNC - 0x00400000), *tr;
    DWORD old;
    int i;

    if (!g_trueXyz || g_projState || !base) return;
    if (IsBadReadPtr(p, sizeof(PROJ_SIG))) { g_projState = 2; return; }
    if (p[0] == 0xE9) {                  /* an earlier load of us got there */
        g_projState = g_projOrig ? 1 : 3;
        return;
    }
    for (i = 0; i < (int)sizeof(PROJ_SIG); i++)
        if (p[i] != PROJ_SIG[i]) { g_projState = 2; return; }

    if (!g_tx) {
        g_tx = (TxEnt *)VirtualAlloc(NULL, sizeof(TxEnt) * TX_SIZE,
                                     MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
        if (!g_tx) { g_projState = 3; return; }
    }
    tr = (BYTE *)VirtualAlloc(NULL, 32, MEM_COMMIT | MEM_RESERVE,
                              PAGE_EXECUTE_READWRITE);
    if (!tr) { g_projState = 3; return; }
    for (i = 0; i < (int)sizeof(PROJ_SIG); i++) tr[i] = p[i];
    tr[8] = 0xE9;
    *(LONG *)(tr + 9) = (LONG)(LONG_PTR)((p + 8) - (tr + 13));
    g_projOrig = (void (__cdecl *)(const void *, void *, DWORD))tr;

    if (!VirtualProtect(p, 8, PAGE_EXECUTE_READWRITE, &old)) {
        g_projState = 3;
        g_projOrig = NULL;
        return;
    }
    p[0] = 0xE9;
    *(LONG *)(p + 1) = (LONG)(LONG_PTR)((BYTE *)projThunk - (p + 5));
    p[5] = p[6] = p[7] = 0x90;
    VirtualProtect(p, 8, old, &old);
    FlushInstructionCache(GetCurrentProcess(), p, 8);
    /* the game now calls into this module on every vertex; it must never be
     * unloaded, and it loads the renderer twice */
    {
        HMODULE keep = NULL;
        GetModuleHandleExA(0x00000001 | 0x00000004, (LPCSTR)(void *)projThunk, &keep);
    }
    g_projState = 1;
}

/* the four "this corner is behind the near plane, drop the polygon" jumps in
 * 0x00442560. With the corners coming from the hook they are no longer a
 * reason to drop anything. */
#define BEHIND_N 4
static const DWORD BEHIND_AT[BEHIND_N] =
    { 0x004425A7, 0x004425BC, 0x004425D1, 0x004425E6 };
static const BYTE BEHIND_SIG[BEHIND_N][6] = {
    { 0x0F,0x8E,0x8E,0x03,0x00,0x00 },
    { 0x0F,0x8E,0x79,0x03,0x00,0x00 },
    { 0x0F,0x8E,0x64,0x03,0x00,0x00 },
    { 0x0F,0x8E,0x4F,0x03,0x00,0x00 },
};
static volatile LONG g_behindState;  /* 0 off, 1 patched, 2 not found, 3 denied */

static void patchBehind(BYTE *base)
{
    int n, i, done = 0;
    if (!g_behindOn || !g_trueXyz || g_behindState || !base) return;
    for (n = 0; n < BEHIND_N; n++) {
        BYTE *p = base + (BEHIND_AT[n] - 0x00400000);
        DWORD old;
        if (IsBadReadPtr(p, 6)) { g_behindState = 2; return; }
        for (i = 0; i < 6; i++) if (p[i] != 0x90) break;
        if (i == 6) { done++; continue; }            /* already ours */
        for (i = 0; i < 6; i++) if (p[i] != BEHIND_SIG[n][i]) break;
        if (i != 6) { g_behindState = 2; return; }
        if (!VirtualProtect(p, 6, PAGE_EXECUTE_READWRITE, &old)) {
            g_behindState = 3;
            return;
        }
        for (i = 0; i < 6; i++) p[i] = 0x90;
        VirtualProtect(p, 6, old, &old);
        FlushInstructionCache(GetCurrentProcess(), p, 6);
        done++;
    }
    g_behindState = (done == BEHIND_N) ? 1 : 2;
}

/* ------------------------------------------------------ 360: cube passes
 *
 * The engine deletes anything nearer than the near plane (0x00445BE0 writes
 * zeros, 0x00442560 drops the polygon on any zero w, 0x00443CC0 drops it when
 * all four are zero and clips it in 0x00442960 when some are). Everything the
 * projection can hold - the whole hemisphere in front of the eye, because the
 * screen rectangle test 0x00442500 is already stubbed - comes through as
 * honest projected quads that unproject() already turns back into 3D.
 *
 * So instead of fighting the projection, turn the camera. After the engine's
 * own world pass (0x00440D00) the same lists are drawn five more times with
 * the view matrix rotated ninety degrees at a time: back, left, right, up,
 * down. Each pass sees its own front hemisphere, projected and clipped by the
 * engine's own code, nothing patched. The rotation is applied AFTER the
 * camera, in view space, by post-multiplying the matrix on top of the stack
 * (0x004CF22C, 4 rows of 3 floats, row vector convention: 0x00442430 computes
 * out = v.x*row0 + v.y*row1 + v.z*row2 + row3) with a matrix of 0/+-1, so
 * the rotated view coordinates are bit exact permutations of the true ones.
 * The camera itself is applied by 0x004084B0, which every renderer calls;
 * that one is detoured so that the chunk pass 0x00440C70 (chunk matrix, then
 * camera) picks up the rotation as well.
 *
 * A quad in the front-right quadrant is fully in front of the eye in the
 * front pass AND in the right pass, so it arrives twice. Each arrival is
 * unrotated into the true view space, scored against the six cube axes
 * (the smallest cosine over its four corners, per axis) and kept only in the
 * pass whose axis scores best. Deterministic, no hashing, no duplicates, and
 * the kept copy is the one whose corners are all within a cube corner's
 * angle (~55 degrees) of the axis, so nothing is ever near the +-10000 clamp.
 * Only a polygon that straddles all six near planes at once - one that wraps
 * around the eye - is lost, and that one was inside a wall anyway.
 *
 * The lists behind the cursor (cityback) are drawn in the rotated passes and
 * in one extra front pass; never in the engine's own pass, so the game window
 * and HGL_D3D's 3000-quad wall see exactly what they saw before. Quads of the
 * extra passes never reach HGL_D3D at all.
 *
 * Depth: a rotated pass has w along its own axis. Every world quad - the
 * engine's own front pass included, when passes are on - gets its sort key
 * and per vertex depth from the RADIAL distance instead, which is the same
 * number in every pass.
 *
 * NOT VERIFIED ON A LIVE RUN. passes defaults to 0. */
static int      g_cityAhead;            /* defined below with the city patch    */
static int      g_passOn;               /* [view] passes                       */
static int      g_cityBack;             /* [view] cityback: lists behind cursor */
static int      g_passUpDown = 1;       /* [view] passupdown                   */
static volatile LONG g_pass;            /* 0 engine, 1..5 rotated, 6 front extra */
static volatile LONG g_passDir;         /* rotation the camera hook applies    */
static volatile LONG g_inWorld;         /* inside 0x00440D00 (any pass)        */
static volatile LONG g_camState, g_worldState;  /* 0 off 1 hooked 2 nosig 3 denied */
static DWORD    g_passSeen[8], g_passKept[8], g_passSeenS[8], g_passKeptS[8];
static DWORD    g_passBackLists, g_passBackListsS, g_passTicks;
static DWORD    g_worldCalls, g_worldCallsS;
static double   g_passMsOrig, g_passMsExtra, g_passMsOrigS, g_passMsExtraS;
static DWORD    g_nonWorldQ, g_nonWorldQS;
static DWORD    g_nwRa[6], g_nwRaN[6], g_nwRaS[6], g_nwRaNS[6];
static int      g_nwN, g_nwNS;

/* game view space: x right, y down, z forward. r x u = f for every entry. */
static const float PASS_R[6][3] = { { 1,0,0}, {-1,0,0}, { 0,0,1}, { 0,0,-1}, { 1,0,0}, { 1,0,0} };
static const float PASS_U[6][3] = { { 0,1,0}, { 0,1,0}, { 0,1,0}, { 0,1,0}, { 0,0,1}, { 0,0,-1} };
static const float PASS_F[6][3] = { { 0,0,1}, { 0,0,-1}, {-1,0,0}, { 1,0,0}, { 0,-1,0}, { 0,1,0} };

/* ---- pass dedup by identity, not by geometry ----
 * The old resolver decided from a quad's DIRECTION which pass "should" own
 * it, and dropped it from every other pass. That assumed the owner pass
 * would actually draw it, which is false in two ways: the native pass never
 * gets the cityback chunks (so a back chunk that curves round to the side or
 * front was assigned to the front and drawn by nobody), and with citymemory
 * off the down pass has no near lists of its own. Both showed up as holes.
 * This instead records every quad that reached the output this frame
 * (texture + true view-space centroid + one corner) and lets each later
 * pass draw only what nobody has drawn yet. Native pass first, so the
 * engine's own projection always wins where it exists. */
#define PDD_N 8192
typedef struct { float c[3], k[4][3]; DWORD tex; int next; BYTE pass; } PddEnt;
static PddEnt   g_pdd[PDD_N];
static int      g_pddN;
static int      g_pddHead[4096];
static int      g_passDedup = 1;        /* [view] passdedup                    */
static int      g_passTol = 3;          /* [view] passtol: match slack, units  */
static DWORD    g_pddDup, g_pddDupS, g_pddFull, g_pddFullS;
/* [probe] rear quads eaten by the filter: who ate them. First 8 per window.
 * dist/tol are the numbers the match was decided with; w0 is the raw first
 * corner depth word, to catch a wrong w decode in the same run. */
typedef struct { DWORD tex; float cc[3], ec[3]; int cpass, epass;
                 float dist, tol; DWORD w0; } PddKill;
static PddKill  g_pddKill[8]; static LONG g_pddKillN;
/* [probe] cross-pass kills whose two centroids differ by more than one unit:
 * with an honest table these do not exist (the offline reproduction eats only
 * byte-identical duplicates), so anything here IS the false match. */
static PddKill  g_pddXKill[8]; static LONG g_pddXKillN;
/* [probe] quads whose unrotated centroid does not point down the pass's own
 * axis, counted per pass BEFORE dedup. A 60-degree pass can only put corner
 * quads a little off axis; big numbers here mean the rotation chain is not
 * what we think it is. */
static DWORD    g_passOffAxis[8], g_passOffAxisS[8];
/* [probe] live projection sampled at the first quad of each pass per window:
 * if the game walks fx or cx between the native pass and ours, unprojection
 * and projection stop describing the same camera. */
static float    g_passFx[8], g_passCxS[8]; static DWORD g_passFxSeen;
static float    g_passFxS[8], g_passCx[8]; static DWORD g_passFxSeenS;

static void pddClear(void)
{
    int i;
    g_pddN = 0;
    for (i = 0; i < 4096; i++) g_pddHead[i] = -1;
}

/* px/py/pz already in true view space. 1 = a pass already drew this quad.
 * candrop = 0 for the native pass: it registers what it draws but NOTHING is
 * ever taken away from it. The engine's own pass legitimately contains
 * duplicates (consecutive chunk lists overlap at their seams - the original
 * renderer just overdrew them), and the first cut of this filter treated
 * those as "already drawn" and gutted the road in front: front 2098/1027 in
 * the log. The native picture must be byte-for-byte what the flat game shows;
 * only the extra passes skip what is already on screen. */
static int pddSeen(DWORD tex, const float *px, const float *py, const float *pz, int candrop, DWORD w0)
{
    float c[3] = { 0, 0, 0 }, tol, tol2, dist;
    int i, h, e;
    for (i = 0; i < 4; i++) { c[0] += px[i]; c[1] += py[i]; c[2] += pz[i]; }
    c[0] *= 0.25f; c[1] *= 0.25f; c[2] *= 0.25f;
    dist = (float)sqrt((double)(c[0]*c[0] + c[1]*c[1] + c[2]*c[2]));
    /* screen x/y arrive as whole pixels, so the unprojection error grows
     * with distance: about one pixel's worth, plus a fixed floor */
    tol = (float)g_passTol + 1.5f * dist / (g_fx > 1.0f ? g_fx : 554.3f);
    tol2 = tol * tol;
    h = (int)(tex & 4095);
    for (e = g_pddHead[h]; e >= 0; e = g_pdd[e].next) {
        const PddEnt *p = &g_pdd[e];
        float dx, dy, dz;
        int j, hit = 0;
        if (p->tex != tex) continue;
        dx = p->c[0] - c[0]; dy = p->c[1] - c[1]; dz = p->c[2] - c[2];
        if (dx*dx + dy*dy + dz*dz > tol2) continue;
        for (j = 0; j < 4 && !hit; j++) {
            dx = p->k[j][0] - px[0]; dy = p->k[j][1] - py[0]; dz = p->k[j][2] - pz[0];
            if (dx*dx + dy*dy + dz*dz <= tol2) hit = 1;
        }
        if (hit) {
            g_pddDup++;
            if (candrop) {
                float ddx = p->c[0] - c[0], ddy = p->c[1] - c[1], ddz = p->c[2] - c[2];
                float dd = ddx*ddx + ddy*ddy + ddz*ddz;
                if (c[2] > 0.0f && g_pddKillN < 8) {
                    LONG w = InterlockedIncrement(&g_pddKillN) - 1;
                    if (w < 8) {
                        g_pddKill[w].tex = tex;
                        g_pddKill[w].cc[0] = c[0]; g_pddKill[w].cc[1] = c[1]; g_pddKill[w].cc[2] = c[2];
                        g_pddKill[w].ec[0] = p->c[0]; g_pddKill[w].ec[1] = p->c[1]; g_pddKill[w].ec[2] = p->c[2];
                        g_pddKill[w].cpass = (int)g_pass; g_pddKill[w].epass = (int)p->pass;
                        g_pddKill[w].dist = dist; g_pddKill[w].tol = tol; g_pddKill[w].w0 = w0;
                    }
                }
                if (dd > 1.0f && (int)p->pass != (int)g_pass && g_pddXKillN < 8) {
                    LONG w = InterlockedIncrement(&g_pddXKillN) - 1;
                    if (w < 8) {
                        g_pddXKill[w].tex = tex;
                        g_pddXKill[w].cc[0] = c[0]; g_pddXKill[w].cc[1] = c[1]; g_pddXKill[w].cc[2] = c[2];
                        g_pddXKill[w].ec[0] = p->c[0]; g_pddXKill[w].ec[1] = p->c[1]; g_pddXKill[w].ec[2] = p->c[2];
                        g_pddXKill[w].cpass = (int)g_pass; g_pddXKill[w].epass = (int)p->pass;
                        g_pddXKill[w].dist = dist; g_pddXKill[w].tol = tol; g_pddXKill[w].w0 = w0;
                    }
                }
            }
            return candrop;
        }
    }
    if (g_pddN >= PDD_N) { g_pddFull++; return 0; }
    e = g_pddN++;
    g_pdd[e].tex = tex;
    g_pdd[e].c[0] = c[0]; g_pdd[e].c[1] = c[1]; g_pdd[e].c[2] = c[2];
    for (i = 0; i < 4; i++) { g_pdd[e].k[i][0] = px[i]; g_pdd[e].k[i][1] = py[i]; g_pdd[e].k[i][2] = pz[i]; }
    g_pdd[e].pass = (BYTE)g_pass;
    g_pdd[e].next = g_pddHead[h];
    g_pddHead[h] = e;
    return 0;
}
/* 0 front  1 back  2 left  3 right  4 up  5 down */

static void (__cdecl *g_camOrig)(void *cam);
static void (__cdecl *g_worldOrig)(void);

#define EXE_CAM_APPLY  0x004084B0   /* push esi / mov esi,[esp+8]            */
#define EXE_WORLD_DRAW 0x00440D00   /* push esi / call 0x00440CC0            */
#define EXE_CHUNK_DRAW 0x00440C70   /* void(list): chunk matrix, camera, list */
#define EXE_LIST_DRAW  0x00440C00   /* void(list): walk one object list       */
#define EXE_MTX_PUSH   0x00441AC0
#define EXE_MTX_POP    0x00441AA0
#define EXE_CUR_A      0x004CF814
#define EXE_CUR_B      0x004CF81C
#define EXE_PAIRS      0x004CF820
#define EXE_SECTION    0x004CF818

/* ---- object memory: every scenery object the engine ever handed to
 * 0x00440C00 in its own pass, keyed by the object pointer. A list record is
 * {obj, x, y, z, flags16}; obj holds absolute geometry, the position is only
 * used by the (stubbed) reject in 0x00440A70. The flyover at the start of a
 * stage walks a list that holds the whole city, so after it the memory does
 * too; the rotated passes then draw from memory whatever lies within
 * cityradius of the camera, one call to 0x00442200-ish 0x004421F0 per
 * object. Cleared when the stage DLL that owns the pointers goes away. */
#define OM_BITS 14
#define OM_SIZE (1 << OM_BITS)
typedef struct { DWORD obj; float x, y, z, r; DWORD seen; DWORD fp[4]; } OmEnt;
static OmEnt   *g_om;
static DWORD    g_omN, g_omDrawn, g_omDrawnS, g_omPurged, g_omBad, g_omSkipped, g_omSkippedS;
static int      g_cityMemory = 1;       /* [view] citymemory                   */
static float    g_cityRadius = 15000.0f;/* [view] cityradius, game units       */
static int      g_omCap = 2500;         /* [view] citymax objects per pass      */
static int      g_omCull = 1;           /* [view] omcull: radius in view units  */
static int      g_omFar  = 1;           /* [view] omfar: also learn the far list*/
static int      g_omLocal = 1;          /* [view] omlocal: reject chunk-local objs */
static DWORD    g_omLocalRej, g_omLocalRejS;
static DWORD    g_omFarAdd, g_omFarAddS;/* objects the far list contributed     */
static DWORD    g_omFarSkip, g_omFarSkipS;/* far records the space check refused*/
static DWORD    g_omFarWalk, g_omFarWalkS;/* far records seen at all            */
static DWORD    g_omFarBad,  g_omFarBadS; /* far records omValid turned down    */
static DWORD    g_omFarNone, g_omFarNoneS;/* frames where the far list was empty*/
static float    g_omFwd = 1.0f;         /* measured world->view forward scale   */
static HMODULE  g_omModule;             /* who owns the pointers               */
static DWORD    g_omCheckTick;

static int omValid(DWORD obj);
static void omClear(void)
{
    if (g_om) ZeroMemory(g_om, sizeof(OmEnt) * OM_SIZE);
    g_omN = 0;
    g_omModule = NULL;
}

static int farOwned(DWORD obj);         /* far-chunk objects are chunk-local:
                                         * the memory must never draw them */

static void omAdd(DWORD obj, float x, float y, float z)
{
    DWORD i, n;
    if (farOwned(obj)) return;
    if (!g_om) {
        g_om = (OmEnt *)VirtualAlloc(NULL, sizeof(OmEnt) * OM_SIZE, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
        if (!g_om) return;
    }
    if (!g_omModule) {
        HMODULE m = NULL;
        if (GetModuleHandleExA(0x00000002 | 0x00000004, (LPCSTR)(DWORD_PTR)obj, &m) && m)
            g_omModule = m;
    }
    i = (obj * 0x9E3779B1u) >> (32 - OM_BITS);
    for (n = 0; n < 32; n++, i = (i + 1) & (OM_SIZE - 1)) {
        OmEnt *e = &g_om[i];
        if (e->obj == obj) { e->seen = 1; return; }
        if (!e->obj) {
            const DWORD *o = (const DWORD *)(DWORD_PTR)obj;
            if (g_omN >= OM_SIZE - 64) return;
            {   /* bounding sphere from the vertex array: the list position is
                 * the object's origin, and a road segment's origin is at one
                 * end of it.
                 *
                 * Chunk-local guard. omDraw draws a remembered object by its
                 * own vertices through the current rotated matrix, with no
                 * chunk matrix - so an object whose vertices are CHUNK-LOCAL
                 * (relative to a chunk origin, not the world) lands wherever
                 * those local coordinates fall, tilted and displaced. Live at
                 * the pier this is the asphalt wedge to the right: a t1842
                 * panel whose corners run from y70 to y1940, drawn 26 m off to
                 * the side of open water where nothing stands. citymemory = 0
                 * makes it vanish because then omDraw never runs. The tell is
                 * the same one the far list already checks (omFarPlausible):
                 * for a world-space object the vertex centre sits within the
                 * object's own span of the record's position; a chunk-local
                 * one is the whole chunk distance away. The near lists never
                 * had the check - "they hold absolute geometry" was almost
                 * always true and the exceptions became the wedges. omlocal =
                 * 1 rejects them (default), 0 keeps the old behaviour. */
                const float *v = (const float *)(DWORD_PTR)o[0];
                DWORD nv = *(const WORD *)&o[3], k;
                float lo[3] = { 1e30f, 1e30f, 1e30f }, hi[3] = { -1e30f, -1e30f, -1e30f };
                float cx3 = x, cy3 = y, cz3 = z, rr = 0.0f;
                for (k = 0; k < nv; k++, v += 3) {
                    int c;
                    for (c = 0; c < 3; c++) { if (v[c] < lo[c]) lo[c] = v[c]; if (v[c] > hi[c]) hi[c] = v[c]; }
                }
                if (nv) {
                    float dx = (hi[0] - lo[0]) * 0.5f, dy = (hi[1] - lo[1]) * 0.5f, dz = (hi[2] - lo[2]) * 0.5f;
                    cx3 = lo[0] + dx; cy3 = lo[1] + dy; cz3 = lo[2] + dz;
                    rr = (float)sqrt((double)(dx*dx + dy*dy + dz*dz));
                    if (g_omLocal) {
                        float px3 = cx3 - x, py3 = cy3 - y, pz3 = cz3 - z;
                        float dd = (float)sqrt((double)(px3*px3 + py3*py3 + pz3*pz3));
                        float span = (hi[0]-lo[0]) + (hi[1]-lo[1]) + (hi[2]-lo[2]);
                        if (dd > span + 2000.0f) { g_omLocalRej++; return; }
                    }
                }
                e->obj = obj; e->x = cx3; e->y = cy3; e->z = cz3; e->r = rr; e->seen = 1;
                e->fp[0] = o[0]; e->fp[1] = o[1]; e->fp[2] = o[2]; e->fp[3] = o[3];
                g_omN++;
            }
            return;
        }
    }
}

static int omKnown(DWORD obj)
{
    DWORD i, n;
    if (!g_om || !obj) return 0;
    i = (obj * 0x9E3779B1u) >> (32 - OM_BITS);
    for (n = 0; n < 32; n++, i = (i + 1) & (OM_SIZE - 1)) {
        if (g_om[i].obj == obj) return 1;
        if (!g_om[i].obj) return 0;
    }
    return 0;
}

/* One record of the FAR list, with a sanity check the near lists do not need.
 * A near-list object holds absolute geometry and the record's position is that
 * object's own origin, so the centre of its vertex array cannot be far from
 * the position. If the far list turned out to be drawn under a chunk matrix of
 * its own, its vertices would be chunk-local, the two would disagree by the
 * whole distance to the chunk, and drawing it from memory - which has no such
 * matrix - would scatter buildings across the map. So measure instead of
 * assuming: omfar = 1 keeps only records where the two agree, omfar = 2 keeps
 * everything, and the log says how many each frame the check refused. */
static int omFarPlausible(const DWORD *rec)
{
    const DWORD *o = (const DWORD *)(DWORD_PTR)rec[0];
    const float *v = (const float *)(DWORD_PTR)o[0];
    DWORD nv = *(const WORD *)&o[3], k;
    float lo[3] = { 1e30f, 1e30f, 1e30f }, hi[3] = { -1e30f, -1e30f, -1e30f };
    float d[3], span, dd;
    int q;
    if (!nv) return 0;
    for (k = 0; k < nv; k++, v += 3)
        for (q = 0; q < 3; q++) { if (v[q] < lo[q]) lo[q] = v[q]; if (v[q] > hi[q]) hi[q] = v[q]; }
    for (q = 0; q < 3; q++) d[q] = (lo[q] + hi[q]) * 0.5f - *(const float *)&rec[1 + q];
    span = (hi[0] - lo[0]) + (hi[1] - lo[1]) + (hi[2] - lo[2]);
    dd = (float)sqrt((double)(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]));
    return dd <= span + 400.0f;
}

static void omLearnFar(const DWORD *list)
{
    int n;
    for (n = 0; n < 4096; n++, list += 5) {
        if (IsBadReadPtr(list, 20)) break;
        if (!list[0]) break;
        g_omFarWalk++;
        if (!omValid(list[0])) { g_omFarBad++; continue; }
        if (!omKnown(list[0])) {
            if (g_omFar == 1 && !omFarPlausible(list)) { g_omFarSkip++; continue; }
            g_omFarAdd++;
        }
        omAdd(list[0], *(const float *)&list[1], *(const float *)&list[2], *(const float *)&list[3]);
    }
}

/* remember one list's records (what the engine's own pass just drew) */
static void omLearnList(const DWORD *list)
{
    int n;
    for (n = 0; n < 4096; n++, list += 5) {
        if (IsBadReadPtr(list, 20)) break;
        if (!list[0]) break;
        if (!omValid(list[0])) continue;
        omAdd(list[0], *(const float *)&list[1], *(const float *)&list[2], *(const float *)&list[3]);
    }
}

static void omLearnNear(BYTE *base)
{
    DWORD *cur = *(DWORD **)(base + (EXE_CUR_B - 0x00400000)), *r;
    int n;
    /* The FAR chunk list (cursor 0x004CF814, drawn by 0x00440C70). With
     * citymemory on the rotated passes draw nothing but this memory, and the
     * memory was learnt from the near lists alone - so every object the engine
     * keeps only in the far list was submitted by no rotated pass at all. The
     * engine's own pass draws it, but only inside its own sixty-degree window;
     * everything of it outside that window is drawn by nobody. What survives
     * in VR is the handful of objects of the same structure that also happen
     * to sit in a near list: pieces standing at their true height with the
     * rest of the building missing. That is the wedges by the ship and the
     * half-drawn pier gates. Learning that list here costs one walk of a list
     * the engine has already built, and its objects then go through exactly
     * the same radius and near-plane tests as every other remembered one.
     * omfar = 0 restores the old behaviour, live. */
    if (g_omFar) {
        DWORD *ca = *(DWORD **)(base + (EXE_CUR_A - 0x00400000));
        if (ca && !IsBadReadPtr(ca, 4) && ca[0] &&
            !IsBadReadPtr((void *)(DWORD_PTR)ca[0], 20))
            omLearnFar((const DWORD *)(DWORD_PTR)ca[0]);
        else
            g_omFarNone++;
    }
    if (!cur || IsBadReadPtr(cur, 8) || !cur[0]) return;
    omLearnList((const DWORD *)(DWORD_PTR)cur[0]);
    r = cur;
    for (n = 0; n < g_cityAhead; n++) {
        if (IsBadReadPtr(r, 16)) break;
        if ((LONG)r[3] == -1) break;
        r += 2;
        if (!r[0] || IsBadReadPtr((void *)(DWORD_PTR)r[0], 4)) break;
        omLearnList((const DWORD *)(DWORD_PTR)r[0]);
    }
}

/* the stage DLL owning the pointers: still there? */
static void omCheckOwner(void)
{
    DWORD t = GetTickCount();
    HMODULE m = NULL;
    if (!g_om || !g_omModule || t - g_omCheckTick < 1000) return;
    g_omCheckTick = t;
    if (!GetModuleHandleExA(0x00000002 | 0x00000004, (LPCSTR)(void *)g_omModule, &m) ||
        m != g_omModule) {
        omClear();
        g_omPurged++;
    }
}

/* an object the engine can still draw: 0x004421F0 reads the vertex array at
 * [obj], the polygon table at [obj+4], the per-polygon record at [obj+8],
 * word[obj+0xC] vertices (stack buffer 0x1F44 bytes = 668 max), word[obj+0xE]
 * low 12 bits polygons. Anything else is a stale pointer into reloaded data. */
static int omValid(DWORD obj)
{
    const DWORD *o = (const DWORD *)(DWORD_PTR)obj;
    DWORD nv, np;
    if (IsBadReadPtr(o, 16)) return 0;
    nv = *(const WORD *)&o[3];
    np = *(const WORD *)((const BYTE *)o + 0xE) & 0xFFF;
    if (nv < 1 || nv > 668 || np < 1 || np > 2000) return 0;
    if (!o[0] || !o[1] || !o[2]) return 0;
    if (IsBadReadPtr((const void *)(DWORD_PTR)o[0], nv * 12)) return 0;
    if (IsBadReadPtr((const void *)(DWORD_PTR)o[1], np * 8)) return 0;
    if (IsBadReadPtr((const void *)(DWORD_PTR)o[2], np * 10)) return 0;
    return 1;
}

/* 0x00440A50: the engine rebuilds the streams from scratch - a new scene. */
static void (__cdecl *g_resetOrig)(void);
static volatile LONG g_resetState;
static DWORD g_omResets;
static DWORD g_omSwept, g_omKilled;
static int omSame(const OmEnt *e)
{
    const DWORD *o = (const DWORD *)(DWORD_PTR)e->obj;
    if (!omValid(e->obj)) return 0;
    return o[0] == e->fp[0] && o[1] == e->fp[1] && o[2] == e->fp[2] && o[3] == e->fp[3];
}
/* a new scene: keep what still reads exactly as it did (the flyover's city
 * survives into the round), drop what was overwritten (the title screen's
 * does not survive a stage load). Mostly dead means all dead. */
static void omSweep(void)
{
    DWORD i, dead = 0, was = g_omN;
    if (!g_om) return;
    for (i = 0; i < OM_SIZE; i++) {
        OmEnt *e = &g_om[i];
        if (!e->obj) continue;
        if (!omSame(e)) { e->obj = 0; g_omN--; dead++; }
    }
    g_omSwept++;
    g_omKilled += dead;
    if (was && dead * 2 > was) { omClear(); g_omPurged++; }
}
static void __attribute__((force_align_arg_pointer)) __cdecl resetThunk(void)
{
    g_omResets++;
    g_resetOrig();
    omSweep();
}

/* draw everything remembered within cityradius of the camera */
static void omDraw(BYTE *base)
{
    void (__cdecl *drawObj)(void *) = (void (__cdecl *)(void *))(base + (0x004421F0 - 0x00400000));
    const float *cam = (const float *)(base + (0x004DB898 - 0x00400000));
    float cx = cam[0], cy = cam[1], cz = cam[2];
    const float *m = *(const float **)(base + MTX_PTR_RVA);   /* rotated for this pass */
    DWORD i;
    int drawn = 0;
    float fs;
    if (!g_om || !g_omModule || !m || IsBadReadPtr(m, 48)) return;
    /* vz below is in VIEW space; e->r came out of the vertex array and is in
     * WORLD units. The view matrix scales world into view by the length of its
     * forward column - measured live at 160 on stage 2 - so comparing the two
     * raw divides the radius by 160, i.e. throws it away, and an object was
     * dropped as soon as its CENTRE went about one world unit behind the pass,
     * however much of it still stuck out in front. omcull = 0 is the old test,
     * for looking at the two side by side without a restart. */
    fs = (float)sqrt((double)(m[2] * m[2] + m[5] * m[5] + m[8] * m[8]));
    if (!(fs > 0.0001f)) fs = 1.0f;
    g_omFwd = fs;
    if (!g_omCull) fs = 1.0f;
    for (i = 0; i < OM_SIZE && drawn < g_omCap; i++) {
        OmEnt *e = &g_om[i];
        float dx, dy, dz, vz, len;
        if (!e->obj) continue;
        dx = e->x - cx; dy = e->y - cy; dz = e->z - cz;
        len = (float)sqrt((double)(dx * dx + dy * dy + dz * dz));
        if (len - e->r > g_cityRadius) continue;
        /* bounding sphere against this pass's near plane: anything with its
         * whole sphere behind the pass cannot contribute a polygon */
        vz = e->x * m[2] + e->y * m[5] + e->z * m[8] + m[11];
        if (vz + e->r * fs < -200.0f) { g_omSkipped++; continue; }
        if (!omSame(e)) { e->obj = 0; g_omN--; g_omBad++; continue; }
        g_probeObj = e->obj;
        {   /* the object's own game-space Y range: a flat tile spans almost
             * nothing, and none of its quads can then reach into the sky - so
             * pushQuad can throw out a "flat object" quad that does (the alias
             * wedge, proven by the probe: objY -11..-11, quad raised +1221). */
            const DWORD *oo = (const DWORD *)(DWORD_PTR)e->obj;
            const float *vv = (const float *)(DWORD_PTR)oo[0];
            DWORD nvv = *(const WORD *)&oo[3], kk;
            float ylo = 1e30f, yhi = -1e30f;
            g_probeFlat = 0;
            if (vv && nvv && nvv <= 668 && !IsBadReadPtr(vv, nvv * 12)) {
                for (kk = 0; kk < nvv; kk++, vv += 3) {
                    if (vv[1] < ylo) ylo = vv[1];
                    if (vv[1] > yhi) yhi = vv[1];
                }
                g_probeYlo = ylo; g_probeYhi = yhi;
                if (yhi - ylo < 300.0f) g_probeFlat = 1;
            }
        }
        drawObj((void *)(DWORD_PTR)e->obj);
        g_probeObj = 0;
        g_probeFlat = 0;
        drawn++;
    }
    g_omDrawn += (DWORD)drawn;
}

/* ---- floor probe: where is the floor under the feet?
 * Stage 3, the hotel mezzanine: the floor the camera stands on is drawn by
 * nobody and the lobby shows through it. The memory holds every list of the
 * section, so either the floor is in a list the memory refuses, or it is in
 * no list at all and the flat game never needed it (its window never looks
 * down). This walks the section's near and far tables, every record, and
 * prints the flat objects whose footprint holds the camera - which list, which
 * key, remembered or not, and whether the object drawer was ever handed it
 * OUTSIDE a list walk (the direct path, see objThunk). Then it walks the
 * object header table itself, so an object that sits in no list is named too.
 * [view] floorprobe, live; ~40 lines every two seconds while on. */
static int   g_floorProbe;
static int   g_feetFill;                /* [view] feetfill: radius in metres, 0 off */
static int   g_feetDrop = 3;            /* [view] feetdrop: cm under the real floor */
static int   g_feetLog;                 /* filled in by pushFeetFill for the log   */
static float g_feetLogH;
static DWORD g_feetLogN, g_feetLogNS;

/* the object drawer 0x004421F0, detoured: every model the game draws goes
 * through here - from a list walk (inside 0x00440D00, g_inWorld) or straight
 * from game logic (the direct path). The direct ones are remembered by
 * pointer, nothing more, so the probe can say "this floor was drawn directly
 * during the flyover" if it ever was. */
static void (__cdecl *g_objOrig)(void *);
static volatile LONG g_objHookState;    /* 0 off 1 hooked 2 nosig 3 denied */
#define DIRECT_BITS 12
static DWORD g_direct[1 << DIRECT_BITS];
static DWORD g_directN, g_directCalls, g_directCallsS;

static int directFind(DWORD obj, int add)
{
    DWORD i = (obj * 0x9E3779B1u) >> (32 - DIRECT_BITS), n;
    if (!obj) return 0;
    for (n = 0; n < 64; n++, i = (i + 1) & ((1 << DIRECT_BITS) - 1)) {
        if (g_direct[i] == obj) return 1;
        if (!g_direct[i]) {
            if (!add || g_directN >= (1 << DIRECT_BITS) - 128) return 0;
            g_direct[i] = obj; g_directN++;
            return 1;
        }
    }
    return 0;
}

static void __attribute__((force_align_arg_pointer)) __cdecl objThunk(void *obj)
{
    if (!g_inWorld) { g_directCalls++; directFind((DWORD)(DWORD_PTR)obj, 1); }
    g_objOrig(obj);
}

/* bounding box of an object's vertex array; 0 if it is not an object */
static int objBox(DWORD obj, float *lo, float *hi)
{
    const DWORD *o = (const DWORD *)(DWORD_PTR)obj;
    const float *v;
    DWORD nv, k;
    int c;
    if (!omValid(obj)) return 0;
    v = (const float *)(DWORD_PTR)o[0];
    nv = *(const WORD *)&o[3];
    for (c = 0; c < 3; c++) { lo[c] = 1e30f; hi[c] = -1e30f; }
    for (k = 0; k < nv; k++, v += 3)
        for (c = 0; c < 3; c++) { if (v[c] < lo[c]) lo[c] = v[c]; if (v[c] > hi[c]) hi[c] = v[c]; }
    return (int)nv;
}

/* one record against the camera: flat, footprint holds the camera (margin),
 * within 4 units of its height. Prints a line when it does. */
static int floorProbeRec(HANDLE h, DWORD obj, const float *cam, const char *tag, int idx, DWORD key,
                         DWORD *minObj, DWORD *maxObj, int *lines)
{
    float lo[3], hi[3];
    char b[256]; DWORD w;
    int nv = objBox(obj, lo, hi);
    if (!nv) return 0;
    if (obj < *minObj) *minObj = obj;
    if (obj > *maxObj) *maxObj = obj;
    if (hi[1] - lo[1] > 0.35f) return 0;
    if (cam[0] < lo[0] - 1.0f || cam[0] > hi[0] + 1.0f) return 0;
    if (cam[2] < lo[2] - 1.0f || cam[2] > hi[2] + 1.0f) return 0;
    if (lo[1] - cam[1] > 4.0f || cam[1] - hi[1] > 4.0f) return 0;
    if (*lines >= 40) return 1;
    (*lines)++;
    wsprintfA(b, "  fp %s%d k%u obj %08X nv %d y %d.%02d dy %d.%02d x %d..%d z %d..%d known %d direct %d far %d\r\n",
              tag, idx, key, obj, nv,
              (int)lo[1], abs((int)(lo[1] * 100)) % 100,
              (int)(lo[1] - cam[1]), abs((int)((lo[1] - cam[1]) * 100)) % 100,
              (int)lo[0], (int)hi[0], (int)lo[2], (int)hi[2],
              omKnown(obj), directFind(obj, 0), farOwned(obj));
    WriteFile(h, b, lstrlenA(b), &w, NULL);
    return 1;
}

static void floorProbeLog(HANDLE h)
{
    BYTE *base = (BYTE *)GetModuleHandleA(NULL);
    const float *cam;
    DWORD *pairs, *curA, *curB, *tab;
    int idx, n, lines = 0, lists = 0, recs = 0, hits = 0;
    DWORD minObj = 0xFFFFFFFFu, maxObj = 0, w;
    char b[512];
    if (!base) return;
    cam   = (const float *)(base + (0x004DB898 - 0x00400000));
    pairs = *(DWORD **)(base + (EXE_PAIRS - 0x00400000));
    curA  = *(DWORD **)(base + (EXE_CUR_A - 0x00400000));
    curB  = *(DWORD **)(base + (EXE_CUR_B - 0x00400000));
    idx   = *(short *)(base + (EXE_SECTION - 0x00400000));
    if (IsBadReadPtr(cam, 12) || !pairs || idx < 0 || idx > 64 || IsBadReadPtr(pairs + idx * 2, 8)) return;
    wsprintfA(b, "floorprobe cam %d.%02d %d.%02d %d.%02d sec %d curB %08X curA %08X near %08X far %08X direct %u calls %u hook %d\r\n",
              (int)cam[0], abs((int)(cam[0] * 100)) % 100, (int)cam[1], abs((int)(cam[1] * 100)) % 100,
              (int)cam[2], abs((int)(cam[2] * 100)) % 100, idx, (DWORD)(DWORD_PTR)curB, (DWORD)(DWORD_PTR)curA,
              pairs[idx * 2], pairs[idx * 2 + 1], g_directN, g_directCallsS, (int)g_objHookState);
    WriteFile(h, b, lstrlenA(b), &w, NULL);
    for (n = 0; n < 2; n++) {
        int e;
        tab = (DWORD *)(DWORD_PTR)pairs[idx * 2 + n];
        if (!tab || IsBadReadPtr(tab, 8)) continue;
        for (e = 0; e < 256; e++, tab += 2) {
            const DWORD *r;
            int k;
            if (IsBadReadPtr(tab, 8) || tab[1] == 0xFFFFFFFFu) break;
            if (!tab[0] || IsBadReadPtr((void *)(DWORD_PTR)tab[0], 20)) continue;
            lists++;
            r = (const DWORD *)(DWORD_PTR)tab[0];
            for (k = 0; k < 4096; k++, r += 5) {
                if (IsBadReadPtr(r, 20) || !r[0]) break;
                recs++;
                hits += floorProbeRec(h, r[0], cam, n ? "F" : "N", e, tab[1], &minObj, &maxObj, &lines);
            }
        }
    }
    /* the header table: 16-byte records, contiguous, between the lowest and
     * highest object any list named. Anything flat under the camera that no
     * list holds is printed with tag "H". */
    if (maxObj > minObj && maxObj - minObj < 0x40000) {
        DWORD o;
        int seen = 0;
        for (o = minObj; o <= maxObj; o += 16) {
            float lo[3], hi[3];
            if (!objBox(o, lo, hi)) continue;
            seen++;
            if (hi[1] - lo[1] > 0.35f) continue;
            if (cam[0] < lo[0] - 1.0f || cam[0] > hi[0] + 1.0f) continue;
            if (cam[2] < lo[2] - 1.0f || cam[2] > hi[2] + 1.0f) continue;
            if (lo[1] - cam[1] > 4.0f || cam[1] - hi[1] > 4.0f) continue;
            if (lines >= 48) break;
            lines++;
            wsprintfA(b, "  fp H obj %08X y %d.%02d dy %d.%02d x %d..%d z %d..%d known %d direct %d far %d\r\n",
                      o, (int)lo[1], abs((int)(lo[1] * 100)) % 100,
                      (int)(lo[1] - cam[1]), abs((int)((lo[1] - cam[1]) * 100)) % 100,
                      (int)lo[0], (int)hi[0], (int)lo[2], (int)hi[2],
                      omKnown(o), directFind(o, 0), farOwned(o));
            WriteFile(h, b, lstrlenA(b), &w, NULL);
        }
        wsprintfA(b, "  fp headers %08X..%08X valid %d\r\n", minObj, maxObj, seen);
        WriteFile(h, b, lstrlenA(b), &w, NULL);
    }
    wsprintfA(b, "  fp lists %d records %d underfoot %d | feetfill %d drop %d proto %d h %d.%02dm copies %u\r\n",
              lists, recs, hits, g_feetFill, g_feetDrop, g_feetLog,
              (int)g_feetLogH, abs((int)(g_feetLogH * 100)) % 100, g_feetLogNS);
    WriteFile(h, b, lstrlenA(b), &w, NULL);
}
/* where the kept quads of each pass actually point, by centroid */
static DWORD    g_passDirHist[8][6], g_passDirHistS[8][6];
static float    g_passSample[8][7][4], g_passSampleS[8][7][4];   /* sx,sy,w,px,py,pz + one */
static int      g_passSampleOk[8], g_passSampleOkS[8];
static volatile LONG g_passStage;       /* where inside worldThunk we are      */
static int      g_passA = 0, g_passB = 1;   /* [view] passa / passb            */

/* ---- passdump: the kept quads of one pass, with everything that decided
 * their shape. A colour ramp says WHICH BAND; this says which quad, where its
 * corners are, and whether the fault is already there before passUnrotate or
 * appears in it. One line per quad:
 *   p<pass> t<texture> L<layer> <src> d<metres> y<height>
 *       | the four corners in the PASS's own view space
 *       | the same four after passUnrotate, in the native one
 * src: h = a whole quad from the projector hook, x = a piece the clipper
 * detour cut up. The buffer fills over several frames and is flushed with the
 * two-second log block. */
#define PDUMP_MAX 60
static char     g_pdBuf[PDUMP_MAX][256];
static int      g_pdN;
static int      g_passDump;             /* [view] passdump: 0 off, 1..6 pass, 7 any */
static int      g_dumpY;                /* [view] dumpy: only above this height     */
static int      g_passDumpN = 40;       /* [view] passdumpn                         */
static float    g_upm = 134.0f;

static void passDumpAdd(int pass, DWORD tex, DWORD layer, char src,
                        const float *bx, const float *by, const float *bz,
                        const float *ax, const float *ay, const float *az)
{
    char *p;
    int i, d;
    float fy = 0.0f, cx = 0.0f, cz = 0.0f;
    if (g_pdN >= g_passDumpN || g_pdN >= PDUMP_MAX) return;
    for (i = 0; i < 4; i++) { fy += ay[i]; cx += ax[i]; cz += az[i]; }
    fy *= 0.25f; cx *= 0.25f; cz *= 0.25f;
    if (fy < (float)g_dumpY) return;
    d = (int)(sqrt((double)(cx * cx + fy * fy + cz * cz)) / (double)(g_upm > 1.0f ? g_upm : 134.0f));
    p = g_pdBuf[g_pdN];
    p += wsprintfA(p, "  p%d t%u L%u %c d%dm y%d |", pass, tex, layer, src, d, (int)fy);
    for (i = 0; i < 4; i++) p += wsprintfA(p, " %d,%d,%d", (int)bx[i], (int)by[i], (int)bz[i]);
    p += wsprintfA(p, " |");
    for (i = 0; i < 4; i++) p += wsprintfA(p, " %d,%d,%d", (int)ax[i], (int)ay[i], (int)az[i]);
    wsprintfA(p, "\r\n");
    g_pdN++;
}
static volatile LONG g_excHooked;

static void exactFrameClear(void);
static int g_passLogVerbose;            /* [view] passlogverbose */
static int g_shotLog;                   /* [view] shotlog: VC2VR_SHOT.LOG sprite dump after each shot */
static int g_passLogFresh;
static void passLog(const char *line)
{
    /* one run, one log: the first write of a session truncates */
    HANDLE h = CreateFileA("VC2VR_PASS.LOG", g_passLogFresh ? FILE_APPEND_DATA : GENERIC_WRITE,
                           FILE_SHARE_READ, NULL, g_passLogFresh ? OPEN_ALWAYS : CREATE_ALWAYS,
                           FILE_ATTRIBUTE_NORMAL, NULL);
    g_passLogFresh = 1;
    if (h != INVALID_HANDLE_VALUE) {
        DWORD w;
        WriteFile(h, line, lstrlenA(line), &w, NULL);
        CloseHandle(h);
    }
}

/* one data point instead of a guess: what died, where, in which pass */
static LONG WINAPI passExcHandler(EXCEPTION_POINTERS *ep)
{
    static volatile LONG once;
    DWORD code = ep->ExceptionRecord->ExceptionCode;
    if (code == 0xE06D7363 || code == 0x40010006 || code == DBG_PRINTEXCEPTION_C ||
        code == 0x406D1388) return EXCEPTION_CONTINUE_SEARCH;
    if (InterlockedIncrement(&once) == 1) {
        char b[400];
        DWORD eip = ep->ContextRecord->Eip;
        BYTE *base = (BYTE *)GetModuleHandleA(NULL);
        HMODULE me = g_self;
        wsprintfA(b, "EXC code %08X eip %08X (exe+%08X, dll+%08X) access %08X | "
                     "pass %d dir %d stage %d inworld %d esp %08X eax %08X ecx %08X edx %08X\r\n",
                  code, eip, (DWORD)(eip - (DWORD)(DWORD_PTR)base),
                  (DWORD)(eip - (DWORD)(DWORD_PTR)me),
                  ep->ExceptionRecord->NumberParameters > 1 ?
                      (DWORD)ep->ExceptionRecord->ExceptionInformation[1] : 0,
                  (int)g_pass, (int)g_passDir, (int)g_passStage, (int)g_inWorld,
                  ep->ContextRecord->Esp, ep->ContextRecord->Eax,
                  ep->ContextRecord->Ecx, ep->ContextRecord->Edx);
        passLog(b);
        {   /* a few return addresses off the stack, to see who called what */
            DWORD *sp = (DWORD *)(DWORD_PTR)ep->ContextRecord->Esp;
            int i, n = 0;
            char *p = b;
            p += wsprintfA(p, "stack:");
            for (i = 0; i < 400 && n < 12; i++) {
                DWORD v;
                if (IsBadReadPtr(sp + i, 4)) break;
                v = sp[i];
                if (v >= 0x00401000 && v < 0x0044D000) { p += wsprintfA(p, " %08X", v); n++; }
            }
            wsprintfA(p, "\r\n");
            passLog(b);
        }
    }
    return EXCEPTION_CONTINUE_SEARCH;
}


static void passRotateTop(BYTE *base, int dir)
{
    float *m = *(float **)(base + MTX_PTR_RVA);
    int i;
    if (!m || IsBadWritePtr(m, 48)) return;
    for (i = 0; i < 4; i++) {
        float *row = m + i * 3;
        float x = row[0], y = row[1], z = row[2];
        row[0] = x * PASS_R[dir][0] + y * PASS_R[dir][1] + z * PASS_R[dir][2];
        row[1] = x * PASS_U[dir][0] + y * PASS_U[dir][1] + z * PASS_U[dir][2];
        row[2] = x * PASS_F[dir][0] + y * PASS_F[dir][1] + z * PASS_F[dir][2];
    }
}

/* ------------------------------------------------------- which way is up
 * Row j of the game's 4x3 view matrix is the view-space image of world axis
 * j: omDraw already leans on that (vz = x*m[2] + y*m[5] + z*m[8] + m[11]).
 * So row 1 is the world's vertical seen from the camera, and when the camera
 * pitches or banks it stops being the view's own y. Everything we INVENT -
 * the sky cylinder and the ground slab - was built square to the view, so on
 * a tilted camera the invented horizon crossed the real one and the slab rose
 * over half the sky. Read the axis once per frame, in the native pass, before
 * passRotateTop turns the matrix for the cube passes. */
static float g_upV[3] = { 0.0f, 1.0f, 0.0f };   /* build space: x right, y up, z back */
static float g_wZ[3]  = { 0.0f, 0.0f, -1.0f };  /* world +Z, in build space          */
static float g_wX[3]  = { 1.0f, 0.0f,  0.0f };  /* world +X, in build space          */
static float g_camAz;                           /* camera heading, world radians     */
static float g_camRightAz;                      /* bearing of the camera's right axis */
static int   g_levelWorld = 1;                  /* [view] levelworld */
static int   g_upOk;
static int   g_upFail;          /* 1 no pointer, 2 unreadable, 3 not a rotation, 4 not upright */
static float g_upRow[12];       /* what was actually read, for the log */
static int   g_upFrame;         /* captured already this frame */
static float g_upScale;         /* length of the matrix row, for the log */

static void captureUp(BYTE *base)
{
    const float **pp = (const float **)(base + MTX_PTR_RVA);
    const float *m;
    float u[3], z[3], len, csx, csy, csz;
    if (!base || IsBadReadPtr(pp, 4)) { g_upFail = 1; return; }
    m = *pp;
    if (!m || IsBadReadPtr(m, 48)) { g_upFail = 2; return; }
    {   int q2;                       /* the whole thing, so the layout is a fact */
        for (q2 = 0; q2 < 12; q2++) g_upRow[q2] = m[q2];
    }
    /* THE COLUMNS ARE THE ORTHOGONAL ONES, NOT THE ROWS. Measured from a live
     * frame: the three rows have lengths 10.09, 10.00, 10.92 and rows 0 and 2
     * are three degrees off square, while the three COLUMNS come out 11.00,
     * 10.00, 10.00 and mutually square to four decimal places. That is what
     * the matrix is: the camera's right, down and forward axes in world
     * coordinates, one per column, each with its own scale - eleven on the
     * horizontal, ten on the other two. A row is therefore a world axis seen
     * from the camera with its three components measured in three different
     * units, and normalising it whole (which is what I did) leaves the
     * direction one and a half degrees out and the error swinging with the
     * camera's heading - the sky drifting as you turn, in miniature.
     * Divide each component by its own column's scale first. */
    csx = (float)sqrt((double)(m[0]*m[0] + m[3]*m[3] + m[6]*m[6]));
    csy = (float)sqrt((double)(m[1]*m[1] + m[4]*m[4] + m[7]*m[7]));
    csz = (float)sqrt((double)(m[2]*m[2] + m[5]*m[5] + m[8]*m[8]));
    if (!(csx > 1e-4f) || !(csy > 1e-4f) || !(csz > 1e-4f)) { g_upFail = 3; return; }
    u[0] =  m[3] / csx;                 /* row 1, game view space (y down, z fwd) */
    u[1] = -m[4] / csy;
    u[2] = -m[5] / csz;                 /* -> build space */
    len = (float)sqrt((double)(u[0]*u[0] + u[1]*u[1] + u[2]*u[2]));
    /* THE GUARD WAS THE BUG. It demanded a unit row - "if this is not a
     * rotation, leave it alone" - and the game's rows are scaled by ten, so a
     * perfectly good matrix was thrown away on every single frame and both
     * levelworld and skylock sat inert for three patches. The scale never
     * mattered: every axis below is divided by its own length anyway, and
     * skyFrame squares the frame up afterwards. So the only thing left to
     * check is that there is a direction here at all. */
    g_upScale = csx / csy;              /* the horizontal stretch, ~1.1 */
    if (!(len > 1e-4f) || len > 1e6f) { g_upFail = 3; return; }
    u[0] /= len; u[1] /= len; u[2] /= len;
    if (u[1] < 0.0f) { u[0] = -u[0]; u[1] = -u[1]; u[2] = -u[2]; }  /* up, not down */
    if (u[1] < 0.2f) { g_upFail = 4; return; }   /* past 78 degrees, not a horizon */
    g_upV[0] = u[0]; g_upV[1] = u[1]; g_upV[2] = u[2];
    /* row 2 is world +Z seen from the camera - a fixed direction in the
     * world, which is exactly what the sky has to be nailed to. The third
     * COLUMN, (m[2], m[5], m[8]), is where the camera looks, in world
     * coordinates: omDraw already uses it as the forward axis. Its heading
     * about the vertical is all the sky needs to be placed once. */
    z[0] =  m[6] / csx; z[1] = -m[7] / csy; z[2] = -m[8] / csz;
    len = (float)sqrt((double)(z[0]*z[0] + z[1]*z[1] + z[2]*z[2]));
    if (len > 0.5f && len < 2.0f) {
        g_wZ[0] = z[0] / len; g_wZ[1] = z[1] / len; g_wZ[2] = z[2] / len;
    }
    z[0] =  m[0] / csx; z[1] = -m[1] / csy; z[2] = -m[2] / csz;   /* row 0: world +X */
    len = (float)sqrt((double)(z[0]*z[0] + z[1]*z[1] + z[2]*z[2]));
    if (len > 0.5f && len < 2.0f) {
        g_wX[0] = z[0] / len; g_wX[1] = z[1] / len; g_wX[2] = z[2] / len;
    }
    /* bearings measured from world +Z towards world +X. The camera forward is
     * the third column of the rotation, its right axis the first - which of
     * the two ways round the world runs is then a fact, not an assumption. */
    g_camAz      = (float)atan2((double)m[2], (double)m[8]);
    g_camRightAz = (float)atan2((double)m[0], (double)m[6]);
    g_upFail = 0;
    g_upOk = 1;
}

/* an orthonormal frame with g_upV as its vertical, its forward as close to
 * the view's own forward as the tilt allows, so nothing spins when the
 * camera is level and the two reduce to (1,0,0) and (0,0,-1) exactly */
/* the frame the sky ring turns in: vertical from the world, forward along
 * world +Z once the dome is locked, otherwise the view's own forward */
static void skyFrame(float *up, float *fwd, float *right);

static void upFrame(float *up, float *fwd, float *right)
{
    float d;
    int i;
    if (!g_levelWorld || !g_upOk) {
        up[0] = 0; up[1] = 1; up[2] = 0;
        fwd[0] = 0; fwd[1] = 0; fwd[2] = -1;
        right[0] = 1; right[1] = 0; right[2] = 0;
        return;
    }
    for (i = 0; i < 3; i++) up[i] = g_upV[i];
    fwd[0] = 0; fwd[1] = 0; fwd[2] = -1;
    d = fwd[0]*up[0] + fwd[1]*up[1] + fwd[2]*up[2];
    for (i = 0; i < 3; i++) fwd[i] -= up[i] * d;
    d = (float)sqrt((double)(fwd[0]*fwd[0] + fwd[1]*fwd[1] + fwd[2]*fwd[2]));
    if (d < 1e-3f) { fwd[0] = 1; fwd[1] = 0; fwd[2] = 0;
                     d = fwd[0]*up[0] + fwd[1]*up[1] + fwd[2]*up[2];
                     for (i = 0; i < 3; i++) fwd[i] -= up[i] * d;
                     d = (float)sqrt((double)(fwd[0]*fwd[0] + fwd[1]*fwd[1] + fwd[2]*fwd[2])); }
    for (i = 0; i < 3; i++) fwd[i] /= d;
    right[0] = fwd[1]*up[2] - fwd[2]*up[1];
    right[1] = fwd[2]*up[0] - fwd[0]*up[2];
    right[2] = fwd[0]*up[1] - fwd[1]*up[0];
}

static int      g_skyLockedFwd;         /* set by pushSkyDome before it builds */
static void skyFrame(float *up, float *fwd, float *right)
{
    float d;
    int i;
    upFrame(up, fwd, right);
    if (!g_skyLockedFwd || !g_levelWorld || !g_upOk) return;
    for (i = 0; i < 3; i++) fwd[i] = g_wZ[i];
    d = fwd[0]*up[0] + fwd[1]*up[1] + fwd[2]*up[2];
    for (i = 0; i < 3; i++) fwd[i] -= up[i] * d;
    d = (float)sqrt((double)(fwd[0]*fwd[0] + fwd[1]*fwd[1] + fwd[2]*fwd[2]));
    if (d < 1e-3f) { upFrame(up, fwd, right); return; }   /* looking straight up */
    for (i = 0; i < 3; i++) fwd[i] /= d;
    /* right is world +X, not a cross product: a bearing then means the same
     * thing here as it does in atan2(x, z), whichever way the game's world
     * is handed */
    for (i = 0; i < 3; i++) right[i] = g_wX[i];
    d = right[0]*up[0] + right[1]*up[1] + right[2]*up[2];
    for (i = 0; i < 3; i++) right[i] -= up[i] * d;
    d = right[0]*fwd[0] + right[1]*fwd[1] + right[2]*fwd[2];
    for (i = 0; i < 3; i++) right[i] -= fwd[i] * d;
    d = (float)sqrt((double)(right[0]*right[0] + right[1]*right[1] + right[2]*right[2]));
    if (d < 1e-3f) { upFrame(up, fwd, right); return; }
    for (i = 0; i < 3; i++) right[i] /= d;
}

static void __attribute__((force_align_arg_pointer)) __cdecl camThunk(void *cam)
{
    if (g_passDir > 0) g_passStage = 30;
    g_camOrig(cam);
    if (g_passDir == 0) captureUp((BYTE *)GetModuleHandleA(NULL));
    if (g_passDir > 0) {
        g_passStage = 31;
        passRotateTop((BYTE *)GetModuleHandleA(NULL), (int)g_passDir);
        g_passStage = 32;
    }
}

/* ---- the far chunk, captured at its own draw ----
 * The far cursor 0x004CF814 is a {list, trigger} stream and the record under
 * the cursor at the pier reads list = 0: by the time worldThunk looked, there
 * was nothing to take (walk 0, empty 1 in every live window - the omfar learn
 * read the same dead cursor). The engine itself does not read the cursor when
 * it draws the far chunk either - 0x00440CC0 resolves it ONCE per frame and
 * hands the resolved list to 0x00440C70. So take it where it is known good:
 * a hook on 0x00440C70 remembers the list of the engine's own pass (g_pass
 * == 0), and the rotated passes then draw THAT, chunk matrix, camera and
 * all - 0x00440C70 applies its own chunk matrix (0x4C89C0/0x4C89F0) and its
 * camera call lands in camThunk, which rotates for the current pass. This is
 * what passa always meant to do; it read the cursor too early and drew
 * nothing, and its "characters vanish" cost died when cube-pass quads
 * stopped reaching HGL_D3D's 3000-quad frame list (the g_pass guard in
 * wrap_quad). The far chunk is where the tall harbour structures live -
 * the wedges by the ship are the scraps of them that leaked in through the
 * near lists. */
/* ---- nolifedec: the player cannot die while a probe run is on ----
 * The damage handler (0x0040CE08) takes one word off the player's lives at
 * two sites - 0x0040CE7D and 0x0040CEC4, both "66 FF 4E 28", dec word
 * [esi+0x28] - and calls the death path when the word goes to zero. Found by
 * a two-snapshot diff on a deliberate hit: the live counter is word
 * 0x0052B948 (display copies at 0x004CF1A2/A3). NOPing the two decs keeps
 * every other part of a hit - the flash, the sound, the invulnerability
 * window at [esi+0x2e] - and only the counter stands still. Live key, both
 * directions: 1 patches, 0 puts the original bytes back. For working, not
 * for playing. */
static int g_noLifeDec;                 /* [view] nolifedec                     */
static int g_lifeDecState;              /* 0 original, 1 patched, 2 hands off   */

/* Session 25 learnt the hard way that there is not ONE decrement: the
 * handler at 0x40CE08 carries three (0x40CB7C, 0x40CE7D, 0x40CEC4, 0x40CFEE
 * across its neighbours) and a fifth lives at 0x416F81 as a direct
 * dec word [0x52B8F8] - and the ordinary bullet hit went through a site the
 * first build had not patched. All five now, each verified byte for byte
 * before touching, and on top of that a once-a-second top-up of both lives
 * words back to 7 while the key is on - so even a sixth site nobody has
 * found yet cannot kill the player between two seconds. */
static void lifeDecApply(void)
{
    /* Session 25, third try, and this time from evidence rather than from a
     * disassembly hunch. The five "dec" sites the earlier builds NOPed
     * (0x40CB7C.. and dec word [0x52B8F8]) belong to the AMMUNITION: the
     * word 0x52B8F8 read 6 while the HUD showed seven lives, both before
     * and after the deliberate hit. The only cells in the scanned data
     * segment that actually followed that hit (7 -> 6, live, on the
     * player's own screen) are the bytes at 0x4CF1A2/A3 - fields +2/+3 of
     * the player block at 0x4CF1A0 (stride 0x44, player 2 at 0x4CF1E4).
     * So no code is patched at all any more: while nolifedec is on, the
     * counter is simply written back to 7 every world frame, for a player
     * whose state byte (+1 == 2) says he is in the round. A hit still
     * flashes and still shoves the camera; the byte recovers within a
     * frame, and the death branch never sees a zero. */
    BYTE *pl;
    if (!g_noLifeDec) { g_lifeDecState = 0; return; }
    g_lifeDecState = 1;
    for (pl = (BYTE *)0x004CF1A0; pl <= (BYTE *)0x004CF1E4; pl += 0x44) {
        if (IsBadReadPtr(pl, 4) || IsBadWritePtr(pl, 4)) continue;
        if (pl[1] != 2) continue;               /* not in the round */
        if (pl[2] >= 1 && pl[2] < 7) pl[2] = 7;
        if (pl[3] >= 1 && pl[3] < 7) pl[3] = 7;
    }
}

static void (__cdecl *g_chunkOrig)(void *list);
static volatile LONG g_chunkState;      /* 0 off, 1 hooked, 2 wrong bytes, 3 denied */
static void *g_farListLive;             /* what the engine's own pass just drew  */
static DWORD g_farCaught, g_farCaughtS; /* frames it was seen on                 */

/* Objects of the far chunk are chunk-LOCAL: 0x00440C70 applies its own
 * matrix (0x4C89C0/0x4C89F0) before drawing them, and drawing the same
 * object from the object memory - which applies no such matrix - lands it
 * a constant off in the world. That is what the wedges by the ship really
 * are: not scraps of a building but the SEA (texture 1842), risen 2300
 * units into the sky, drawn by the rotated passes out of a memory the
 * session-24 omfar learning had poisoned - its plausibility check compares
 * the record position with the vertex centre, and for a chunk-local record
 * both are local, so they agree and the check waves the wrong thing in.
 * The cure is a blacklist, filled where the truth is known - at the far
 * chunk's own draw: every object seen in a far list is banned from the
 * memory (purged if already in), and the far chunk reaches the rotated
 * passes only whole, through 0x00440C70, matrix and all (passa). */
#define FOWN_BITS 12
#define FOWN_SIZE (1 << FOWN_BITS)
static DWORD g_farOwn[FOWN_SIZE];
static DWORD g_farOwnN, g_farPurged, g_farPurgedS;

static int farOwned(DWORD obj)
{
    DWORD i, n;
    if (!obj || !g_farOwnN) return 0;
    i = (obj * 0x9E3779B1u) >> (32 - FOWN_BITS);
    for (n = 0; n < 32; n++, i = (i + 1) & (FOWN_SIZE - 1)) {
        if (g_farOwn[i] == obj) return 1;
        if (!g_farOwn[i]) return 0;
    }
    return 0;
}

static void farOwnAdd(DWORD obj)
{
    DWORD i, n;
    if (!obj || g_farOwnN >= FOWN_SIZE - 64) return;
    i = (obj * 0x9E3779B1u) >> (32 - FOWN_BITS);
    for (n = 0; n < 32; n++, i = (i + 1) & (FOWN_SIZE - 1)) {
        if (g_farOwn[i] == obj) return;
        if (!g_farOwn[i]) { g_farOwn[i] = obj; g_farOwnN++; return; }
    }
}

static void omPurgeObj(DWORD obj)
{
    DWORD i, n;
    if (!g_om || !obj) return;
    i = (obj * 0x9E3779B1u) >> (32 - OM_BITS);
    for (n = 0; n < 32; n++, i = (i + 1) & (OM_SIZE - 1)) {
        if (g_om[i].obj == obj) { g_om[i].obj = 0; g_omN--; g_farPurged++; return; }
        if (!g_om[i].obj) return;
    }
}

static void farBlacklist(const DWORD *list)
{
    int n;
    for (n = 0; n < 4096; n++, list += 5) {
        if (IsBadReadPtr(list, 20)) break;
        if (!list[0]) break;
        if (!farOwned(list[0])) {
            farOwnAdd(list[0]);
            omPurgeObj(list[0]);
        }
    }
}

static void __attribute__((force_align_arg_pointer)) __cdecl chunkThunk(void *list)
{
    if (g_pass == 0 && g_inWorld) {
        g_farListLive = list;
        g_farCaught++;
        if (list && !IsBadReadPtr(list, 20))
            farBlacklist((const DWORD *)list);
    }
    g_chunkOrig(list);
}

/* the lists behind the cursor of the near stream, oldest last */
static void passDrawBack(BYTE *base)
{
    DWORD *cur = *(DWORD **)(base + (EXE_CUR_B - 0x00400000)), *r, *pairs, *start;
    int idx, n;
    void (__cdecl *draw)(void *) = (void (__cdecl *)(void *))(base + (EXE_LIST_DRAW - 0x00400000));
    if (g_cityBack <= 0 || !cur || IsBadReadPtr(cur, 8)) return;
    pairs = *(DWORD **)(base + (EXE_PAIRS - 0x00400000));
    idx = *(short *)(base + (EXE_SECTION - 0x00400000));
    if (!pairs || idx < 0 || IsBadReadPtr(pairs + idx * 2, 8)) return;
    start = (DWORD *)(DWORD_PTR)pairs[idx * 2];
    if (!start) return;
    r = cur;
    for (n = 0; n < g_cityBack; n++) {
        r -= 2;
        if (r < start) break;
        if (IsBadReadPtr(r, 8) || !r[0]) break;
        if (IsBadReadPtr((void *)(DWORD_PTR)r[0], 4)) break;
        g_passBackLists++;
        draw((void *)(DWORD_PTR)r[0]);
    }
}

/* the current near list plus the ones ahead, exactly as the engine's own
 * pass gets them from cityThunk */
static void passDrawNear(BYTE *base)
{
    DWORD *cur = *(DWORD **)(base + (EXE_CUR_B - 0x00400000)), *r;
    int n;
    void (__cdecl *draw)(void *) = (void (__cdecl *)(void *))(base + (EXE_LIST_DRAW - 0x00400000));
    if (!cur || IsBadReadPtr(cur, 8) || !cur[0]) return;
    draw((void *)(DWORD_PTR)cur[0]);
    r = cur;
    for (n = 0; n < g_cityAhead; n++) {
        if (IsBadReadPtr(r, 16)) break;
        if ((LONG)r[3] == -1) break;
        r += 2;
        if (!r[0] || IsBadReadPtr((void *)(DWORD_PTR)r[0], 4)) break;
        draw((void *)(DWORD_PTR)r[0]);
    }
}

static void __attribute__((force_align_arg_pointer)) __cdecl worldThunk(void)
{
    BYTE *base = (BYTE *)GetModuleHandleA(NULL);
    int p;
    void (__cdecl *chunk)(void *) = (void (__cdecl *)(void *))(base + (EXE_CHUNK_DRAW - 0x00400000));
    int (__cdecl *push)(void) = (int (__cdecl *)(void))(base + (EXE_MTX_PUSH - 0x00400000));
    int (__cdecl *pop)(void)  = (int (__cdecl *)(void))(base + (EXE_MTX_POP  - 0x00400000));

    LARGE_INTEGER t0, t1, t2, fq;
    g_inWorld = 1;
    g_worldCalls++;
    g_upFrame = 0;
    pddClear();
    exactFrameClear();
    g_passStage = 1;
    g_farListLive = NULL;               /* per frame; the hook refills it */
    lifeDecApply();                     /* nolifedec: top the counter up   */
    QueryPerformanceCounter(&t0);
    g_worldOrig();
    QueryPerformanceCounter(&t1);
    g_passStage = 2;
    if (g_passOn == 1 && g_cityMemory) { omCheckOwner(); g_passStage = 3; omLearnNear(base); }
    if (g_passOn == 1 && g_camState == 1) {
        /* the far chunk of THIS frame, as the engine resolved it (see
         * chunkThunk); the cursor read is only the fallback for a build
         * where the 0x440C70 hook did not take */
        void *listA = (g_chunkState == 1) ? g_farListLive : NULL;
        if (!listA) {
            DWORD *ca = *(DWORD **)(base + (EXE_CUR_A - 0x00400000));
            listA = (ca && !IsBadReadPtr(ca, 4)) ? (void *)(DWORD_PTR)ca[0] : NULL;
        }
        if (listA && IsBadReadPtr(listA, 20)) listA = NULL;
        if (!g_passA) listA = NULL;
        for (p = 1; p <= 5; p++) {
            if (!g_passUpDown && p >= 4) break;
            g_pass = p;
            g_passDir = p;
            g_passStage = 10;
            if (listA) chunk(listA);          /* 0x00440C70: its camera call is ours */
            g_passStage = 11;
            if (g_passB && push()) {
                g_passStage = 12;
                passRotateTop(base, p);
                g_passStage = 13;
                if (g_cityMemory) omDraw(base);
                else passDrawNear(base);
                g_passStage = 14;
                if (!g_cityMemory) passDrawBack(base);
                g_passStage = 15;
                pop();
            }
            g_passStage = 16;
            g_passDir = 0;
        }
        if (g_cityBack > 0 && g_passB && !g_cityMemory && push()) {
            g_pass = 6;
            g_passStage = 20;
            passDrawBack(base);
            pop();
        }
        g_pass = 0;
    }
    QueryPerformanceCounter(&t2);
    QueryPerformanceFrequency(&fq);
    g_passMsOrig  += (double)(t1.QuadPart - t0.QuadPart) * 1000.0 / (double)fq.QuadPart;
    g_passMsExtra += (double)(t2.QuadPart - t1.QuadPart) * 1000.0 / (double)fq.QuadPart;
    g_passStage = 0;
    g_inWorld = 0;
}

static void installPassHooks(BYTE *base)
{
    static const BYTE CAM_SIG[5]   = { 0x56, 0x8B, 0x74, 0x24, 0x08 };
    static const BYTE WORLD_SIG[6] = { 0x56, 0xE8, 0xBA, 0xFF, 0xFF, 0xFF };
    BYTE *p, *tr;
    DWORD old;
    int i;

    if (!g_passOn || g_camState || g_worldState || !base) return;

    /* 0x004084B0 */
    p = base + (EXE_CAM_APPLY - 0x00400000);
    if (IsBadReadPtr(p, 5)) { g_camState = 2; return; }
    for (i = 0; i < 5; i++) if (p[i] != CAM_SIG[i]) { g_camState = 2; return; }
    tr = (BYTE *)VirtualAlloc(NULL, 64, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
    if (!tr) { g_camState = 3; return; }
    for (i = 0; i < 5; i++) tr[i] = p[i];
    tr[5] = 0xE9;
    *(LONG *)(tr + 6) = (LONG)(LONG_PTR)((p + 5) - (tr + 10));
    g_camOrig = (void (__cdecl *)(void *))tr;
    if (!VirtualProtect(p, 5, PAGE_EXECUTE_READWRITE, &old)) { g_camState = 3; return; }
    p[0] = 0xE9;
    *(LONG *)(p + 1) = (LONG)(LONG_PTR)((BYTE *)camThunk - (p + 5));
    VirtualProtect(p, 5, old, &old);
    FlushInstructionCache(GetCurrentProcess(), p, 5);
    g_camState = 1;

    /* 0x00440D00: the prologue holds a relative call, rebuilt in the trampoline */
    p = base + (EXE_WORLD_DRAW - 0x00400000);
    if (IsBadReadPtr(p, 6)) { g_worldState = 2; return; }
    for (i = 0; i < 6; i++) if (p[i] != WORLD_SIG[i]) { g_worldState = 2; return; }
    tr = tr + 16;
    tr[0] = 0x56;
    tr[1] = 0xE8;
    *(LONG *)(tr + 2) = (LONG)(LONG_PTR)((p + 6 + *(LONG *)(p + 2)) - (tr + 6));
    tr[6] = 0xE9;
    *(LONG *)(tr + 7) = (LONG)(LONG_PTR)((p + 6) - (tr + 11));
    g_worldOrig = (void (__cdecl *)(void))tr;
    if (!VirtualProtect(p, 6, PAGE_EXECUTE_READWRITE, &old)) { g_worldState = 3; return; }
    p[0] = 0xE9;
    *(LONG *)(p + 1) = (LONG)(LONG_PTR)((BYTE *)worldThunk - (p + 5));
    p[5] = 0x90;
    VirtualProtect(p, 6, old, &old);
    FlushInstructionCache(GetCurrentProcess(), p, 6);
    g_worldState = 1;
    {
        HMODULE keep = NULL;
        GetModuleHandleExA(0x00000001 | 0x00000004, (LPCSTR)(void *)worldThunk, &keep);
    }
    /* 0x00440A50: mov word ptr [0x4CF818], 0 - nine bytes, relocatable */
    {
        static const BYTE RESET_SIG[9] = { 0x66,0xC7,0x05,0x18,0xF8,0x4C,0x00,0x00,0x00 };
        p = base + (0x00440A50 - 0x00400000);
        if (IsBadReadPtr(p, 9)) { g_resetState = 2; return; }
        for (i = 0; i < 9; i++) if (p[i] != RESET_SIG[i]) { g_resetState = 2; return; }
        tr = tr + 16;
        for (i = 0; i < 9; i++) tr[i] = p[i];
        tr[9] = 0xE9;
        *(LONG *)(tr + 10) = (LONG)(LONG_PTR)((p + 9) - (tr + 14));
        g_resetOrig = (void (__cdecl *)(void))tr;
        if (!VirtualProtect(p, 9, PAGE_EXECUTE_READWRITE, &old)) { g_resetState = 3; return; }
        p[0] = 0xE9;
        *(LONG *)(p + 1) = (LONG)(LONG_PTR)((BYTE *)resetThunk - (p + 5));
        for (i = 5; i < 9; i++) p[i] = 0x90;
        VirtualProtect(p, 9, old, &old);
        FlushInstructionCache(GetCurrentProcess(), p, 9);
        g_resetState = 1;
    }
    /* 0x00440C70: the far-chunk draw. Prologue is one relative call
     * (E8 -> 0x441AC0, the matrix push), rebuilt in the trampoline. */
    {
        static const BYTE CHUNK_SIG[6] = { 0xE8, 0x4B, 0x0E, 0x00, 0x00, 0xA0 };
        p = base + (0x00440C70 - 0x00400000);
        if (IsBadReadPtr(p, 6)) { g_chunkState = 2; return; }
        for (i = 0; i < 6; i++) if (p[i] != CHUNK_SIG[i]) { g_chunkState = 2; return; }
        tr = tr + 16;
        tr[0] = 0xE8;
        *(LONG *)(tr + 1) = (LONG)(LONG_PTR)((p + 5 + *(LONG *)(p + 1)) - (tr + 5));
        tr[5] = 0xE9;
        *(LONG *)(tr + 6) = (LONG)(LONG_PTR)((p + 5) - (tr + 10));
        g_chunkOrig = (void (__cdecl *)(void *))tr;
        if (!VirtualProtect(p, 5, PAGE_EXECUTE_READWRITE, &old)) { g_chunkState = 3; return; }
        p[0] = 0xE9;
        *(LONG *)(p + 1) = (LONG)(LONG_PTR)((BYTE *)chunkThunk - (p + 5));
        VirtualProtect(p, 5, old, &old);
        FlushInstructionCache(GetCurrentProcess(), p, 5);
        g_chunkState = 1;
    }
    /* 0x004421F0: the object drawer. Prologue "mov eax, 0x36B0" (five bytes,
     * no relocation), then a relative call to __chkstk that stays in place.
     * Its own page, the sixty-four bytes above are spent. */
    {
        static const BYTE OBJ_SIG[5] = { 0xB8, 0xB0, 0x36, 0x00, 0x00 };
        BYTE *t2;
        p = base + (0x004421F0 - 0x00400000);
        if (IsBadReadPtr(p, 5)) { g_objHookState = 2; return; }
        for (i = 0; i < 5; i++) if (p[i] != OBJ_SIG[i]) { g_objHookState = 2; return; }
        t2 = (BYTE *)VirtualAlloc(NULL, 64, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
        if (!t2) { g_objHookState = 3; return; }
        for (i = 0; i < 5; i++) t2[i] = p[i];
        t2[5] = 0xE9;
        *(LONG *)(t2 + 6) = (LONG)(LONG_PTR)((p + 5) - (t2 + 10));
        g_objOrig = (void (__cdecl *)(void *))t2;
        if (!VirtualProtect(p, 5, PAGE_EXECUTE_READWRITE, &old)) { g_objHookState = 3; return; }
        p[0] = 0xE9;
        *(LONG *)(p + 1) = (LONG)(LONG_PTR)((BYTE *)objThunk - (p + 5));
        VirtualProtect(p, 5, old, &old);
        FlushInstructionCache(GetCurrentProcess(), p, 5);
        g_objHookState = 1;
    }
}

/* unrotate four corners (OpenXR convention in, out) from pass dir into the
 * true view space and decide whether this pass is the one that keeps them.
 * Returns 0 to drop. */
static void passUnrotate(int dir, float *px, float *py, float *pz)
{
    int i;
    for (i = 0; i < 4; i++) {
        float ax = px[i], ay = -py[i], az = -pz[i];         /* game pass view */
        float vx = ax * PASS_R[dir][0] + ay * PASS_U[dir][0] + az * PASS_F[dir][0];
        float vy = ax * PASS_R[dir][1] + ay * PASS_U[dir][1] + az * PASS_F[dir][1];
        float vz = ax * PASS_R[dir][2] + ay * PASS_U[dir][2] + az * PASS_F[dir][2];
        px[i] = vx; py[i] = -vy; pz[i] = -vz;
    }
}

static int passResolve(int dir, float *px, float *py, float *pz)
{
    float best = -2.0f, mine = -2.0f;
    float sc[6];
    int i, d;
    passUnrotate(dir, px, py, pz);
    for (d = 0; d < 6; d++) {
        sc[d] = 2.0f;
        for (i = 0; i < 4; i++) {
            float vx = px[i], vy = -py[i], vz = -pz[i];
            float len = (float)sqrt((double)(vx*vx + vy*vy + vz*vz));
            float c = len > 1e-6f ?
                (vx*PASS_F[d][0] + vy*PASS_F[d][1] + vz*PASS_F[d][2]) / len : 0.0f;
            if (c < sc[d]) sc[d] = c;
        }
        if (!g_passUpDown && d >= 4) sc[d] = -2.0f;
        if (sc[d] > best) best = sc[d];
    }
    mine = sc[dir];
    return mine >= best - 1e-4f;
}

/* a stable colour per texture id, so surfaces are told apart without textures */
static DWORD tintOf(DWORD tex, DWORD layer)
{
    DWORD h = tex * 2654435761u;
    BYTE r = 90 + ((h >> 0) & 0x7F);
    BYTE g = 90 + ((h >> 8) & 0x7F);
    BYTE b = 90 + ((h >> 16) & 0x7F);
    if (layer == 6) { r = 70; g = 70; b = 80; }        /* ground */
    return 0xFF000000u | (b << 16) | (g << 8) | r;
}

/* ------------------------------------------------------- the world cache ---
 * The game only builds what its own logic decides to build, so anything the
 * camera has driven past is simply gone the next frame. Since every quad
 * arrives tagged with the transform that produced it (PPJ2DD 0x004CF22C), the
 * city can be kept instead of thrown away.
 *
 * The trick is that the object's own placement never has to be known. For a
 * static object the transform is M(t) = Camera(t) . Object, so
 *
 *     D(t) = M(t) . M(t-1)^-1 = Camera(t) . Camera(t-1)^-1
 *
 * with the object cancelling out. Chaining those deltas gives A(t), the
 * camera's motion since the first frame, and A(t)^-1 turns a quad's view
 * space corners into a frame that stands still while the camera moves. That
 * frame is the cache. Quads that turn up at the same place several frames
 * running are scenery and get kept; cars and people never repeat a position
 * and are dropped, which is why they leave no trail.
 */

typedef struct { float m[9], t[3]; int valid; } Xform;   /* m[col*3 + row] */

static void xfIdent(Xform *o)
{
    int i;
    for (i = 0; i < 9; i++) o->m[i] = (i % 4 == 0) ? 1.0f : 0.0f;
    o->t[0] = o->t[1] = o->t[2] = 0.0f;
    o->valid = 1;
}

static void xfApply(const Xform *x, const float *v, float *o)
{
    o[0] = x->m[0] * v[0] + x->m[3] * v[1] + x->m[6] * v[2] + x->t[0];
    o[1] = x->m[1] * v[0] + x->m[4] * v[1] + x->m[7] * v[2] + x->t[1];
    o[2] = x->m[2] * v[0] + x->m[5] * v[1] + x->m[8] * v[2] + x->t[2];
}

static int xfInvert(const Xform *a, Xform *o)
{
    const float *m = a->m;
    float det, inv[9];
    det = m[0] * (m[4] * m[8] - m[7] * m[5])
        - m[3] * (m[1] * m[8] - m[7] * m[2])
        + m[6] * (m[1] * m[5] - m[4] * m[2]);
    if (det > -1e-12f && det < 1e-12f) { o->valid = 0; return 0; }
    det = 1.0f / det;
    inv[0] = (m[4] * m[8] - m[7] * m[5]) * det;
    inv[1] = (m[7] * m[2] - m[1] * m[8]) * det;
    inv[2] = (m[1] * m[5] - m[4] * m[2]) * det;
    inv[3] = (m[6] * m[5] - m[3] * m[8]) * det;
    inv[4] = (m[0] * m[8] - m[6] * m[2]) * det;
    inv[5] = (m[3] * m[2] - m[0] * m[5]) * det;
    inv[6] = (m[3] * m[7] - m[6] * m[4]) * det;
    inv[7] = (m[6] * m[1] - m[0] * m[7]) * det;
    inv[8] = (m[0] * m[4] - m[3] * m[1]) * det;
    {
        int i;
        for (i = 0; i < 9; i++) o->m[i] = inv[i];
        o->t[0] = -(inv[0] * a->t[0] + inv[3] * a->t[1] + inv[6] * a->t[2]);
        o->t[1] = -(inv[1] * a->t[0] + inv[4] * a->t[1] + inv[7] * a->t[2]);
        o->t[2] = -(inv[2] * a->t[0] + inv[5] * a->t[1] + inv[8] * a->t[2]);
    }
    o->valid = 1;
    return 1;
}

/* o = a applied after b */
static void xfMul(const Xform *a, const Xform *b, Xform *o)
{
    float m[9], t[3];
    int c, r;
    for (c = 0; c < 3; c++)
        for (r = 0; r < 3; r++)
            m[c * 3 + r] = a->m[0 * 3 + r] * b->m[c * 3 + 0]
                         + a->m[1 * 3 + r] * b->m[c * 3 + 1]
                         + a->m[2 * 3 + r] * b->m[c * 3 + 2];
    for (r = 0; r < 3; r++)
        t[r] = a->m[0 * 3 + r] * b->t[0] + a->m[1 * 3 + r] * b->t[1]
             + a->m[2 * 3 + r] * b->t[2] + a->t[r];
    for (c = 0; c < 9; c++) o->m[c] = m[c];
    for (r = 0; r < 3; r++) o->t[r] = t[r];
    o->valid = a->valid && b->valid;
}

static float colLen(const float *m, int c)
{
    return (float)sqrt(m[c * 3 + 0] * m[c * 3 + 0] +
                       m[c * 3 + 1] * m[c * 3 + 1] +
                       m[c * 3 + 2] * m[c * 3 + 2]);
}

#define WC_MAX   36000
#define WC_HASH  (1 << 17)
#define WC_KEEP  3            /* frames at one spot before it counts as city */

typedef struct {
    float wx[4], wy[4], wz[4];
    float u[4], v[4];
    DWORD col[4];
    DWORD layer;
    int   seen;
    DWORD lastFrame;
    int   next;               /* hash chain */
} WcQuad;

static WcQuad *g_wc;
static int    *g_wcHead;
static int     g_wcN;
static int     g_wcDrawn, g_wcLive;
static DWORD   g_wcFrame;
static Xform   g_camAcc, g_camAccInv;     /* A(t) and its inverse */
static Xform   g_prevMtx[12];
static int     g_prevMtxN;
static int     g_prevMtxCnt[12];
static int     g_wcTrack;
static int     g_wcHit, g_wcTotal, g_wcMatchRate;

static void wcReset(void)
{
    if (g_wcHead) {
        int i;
        for (i = 0; i < WC_HASH; i++) g_wcHead[i] = -1;
    }
    g_wcN = 0;
    g_prevMtxN = 0;
    xfIdent(&g_camAcc);
    xfIdent(&g_camAccInv);
}

static int wcInit(void)
{
    if (g_wc) return 1;
    g_wc = (WcQuad *)VirtualAlloc(NULL, sizeof(WcQuad) * WC_MAX,
                                  MEM_COMMIT, PAGE_READWRITE);
    g_wcHead = (int *)VirtualAlloc(NULL, sizeof(int) * WC_HASH,
                                   MEM_COMMIT, PAGE_READWRITE);
    if (!g_wc || !g_wcHead) return 0;
    wcReset();
    return 1;
}

static DWORD wcHash(const float *w, DWORD tex)
{
    int qx = (int)(w[0] / 24.0f), qy = (int)(w[1] / 24.0f),
        qz = (int)(w[2] / 24.0f);
    DWORD h = (DWORD)qx * 73856093u ^ (DWORD)qy * 19349663u ^
              (DWORD)qz * 83492791u ^ tex * 2654435761u;
    return h & (WC_HASH - 1);
}

/* keep the accumulated camera a rotation: chained multiplication of a few
 * thousand deltas otherwise stretches it out of shape within a minute */
static void xfOrtho(Xform *x)
{
    float *m = x->m;
    float l0 = colLen(m, 0), d, l;
    int k;
    if (l0 < 1e-6f) return;
    for (k = 0; k < 3; k++) m[k] /= l0;
    d = m[3] * m[0] + m[4] * m[1] + m[5] * m[2];
    for (k = 0; k < 3; k++) m[3 + k] -= d * m[k];
    l = colLen(m, 1);
    if (l < 1e-6f) return;
    for (k = 0; k < 3; k++) m[3 + k] /= l;
    m[6] = m[1] * m[5] - m[2] * m[4];
    m[7] = m[2] * m[3] - m[0] * m[5];
    m[8] = m[0] * m[4] - m[1] * m[3];
}

/* How far did the camera move since the last frame? Any object that stood
 * still and was drawn in both frames answers it: its own placement cancels
 * out of M(t) . M(t-1)^-1. The first version applied that delta once per
 * matching object instead of once per frame, so the camera ran ahead of the
 * game several times over, every remembered corner landed somewhere new, and
 * the cache filled with strangers until it was full - which is exactly the
 * frozen "1/1741" you saw. Now: gather every candidate, keep the ones that
 * agree with each other on the answer, and apply it once. */
static void wcTrackCamera(void)
{
    Xform cand[12], bestD;
    int candN = 0, candCnt[12], i, j, k, best = -1, bestScore = 0;

    g_wcTrack = 0;
    g_wcMatchRate = 0;
    if (g_wcTotal > 0) g_wcMatchRate = g_wcHit * 100 / g_wcTotal;
    g_wcHit = g_wcTotal = 0;

    if (!g_mtxN || !g_prevMtxN) goto done;

    for (i = 0; i < g_mtxN && candN < 12; i++) {
        Xform cur, inv, d;
        float la[3], lb[3];
        for (k = 0; k < 9; k++) cur.m[k] = g_mtx[i].m[k];
        for (k = 0; k < 3; k++) cur.t[k] = g_mtx[i].m[9 + k];
        cur.valid = 1;
        for (k = 0; k < 3; k++) la[k] = colLen(cur.m, k);
        for (j = 0; j < g_prevMtxN; j++) {
            int ok = 1;
            for (k = 0; k < 3; k++) {
                lb[k] = colLen(g_prevMtx[j].m, k);
                if (la[k] < 1e-4f || lb[k] < 1e-4f) { ok = 0; break; }
                if (la[k] / lb[k] < 0.995f || la[k] / lb[k] > 1.005f) { ok = 0; break; }
            }
            if (!ok) continue;
            if (!xfInvert(&g_prevMtx[j], &inv)) continue;
            xfMul(&cur, &inv, &d);
            for (k = 0; k < 3; k++) {
                float l = colLen(d.m, k);
                if (l < 0.99f || l > 1.01f) { ok = 0; break; }
            }
            if (!ok) continue;
            cand[candN] = d;
            candCnt[candN] = g_mtx[i].n;
            candN++;
            break;
        }
    }
    if (!candN) goto done;

    /* the answer several objects agree on is the camera; a lone object that
     * happened to move on its own cannot outvote them */
    for (i = 0; i < candN; i++) {
        int score = candCnt[i];
        for (j = 0; j < candN; j++) {
            float dt, s2 = 0;
            if (i == j) continue;
            for (k = 0; k < 3; k++) {
                dt = cand[i].t[k] - cand[j].t[k];
                s2 += dt * dt;
            }
            if (s2 < 1.0f) score += candCnt[j];
        }
        if (score > bestScore) { bestScore = score; best = i; }
    }
    if (best < 0) goto done;
    bestD = cand[best];
    xfMul(&bestD, &g_camAcc, &g_camAcc);
    xfOrtho(&g_camAcc);
    if (xfInvert(&g_camAcc, &g_camAccInv)) g_wcTrack = 1;

done:
    g_prevMtxN = g_mtxN;
    for (i = 0; i < g_mtxN; i++) {
        for (k = 0; k < 9; k++) g_prevMtx[i].m[k] = g_mtx[i].m[k];
        for (k = 0; k < 3; k++) g_prevMtx[i].t[k] = g_mtx[i].m[9 + k];
        g_prevMtx[i].valid = 1;
        g_prevMtxCnt[i] = g_mtx[i].n;
    }
}

/* our own view axes are x right, y up, z back; the game's are x right,
 * y down, z forward, so two signs flip on the way in and out */
static void wcToGame(const float *o, float *g)
{
    g[0] = o[0]; g[1] = -o[1]; g[2] = -o[2];
}
static void wcFromGame(const float *g, float *o)
{
    o[0] = g[0]; o[1] = -g[1]; o[2] = -g[2];
}

static void wcRemember(const float *px, const float *py, const float *pz,
                       const float *qu, const float *qv, const DWORD *cols,
                       DWORD tex, DWORD layer)
{
    float w[4][3];
    DWORD h;
    int i, idx;

    if (!g_wcOn || !g_wc || !g_wcTrack) return;
    for (i = 0; i < 4; i++) {
        float o[3] = { px[i], py[i], pz[i] }, g[3];
        wcToGame(o, g);
        xfApply(&g_camAccInv, g, w[i]);
    }
    g_wcTotal++;
    h = wcHash(w[0], tex);
    for (idx = g_wcHead[h]; idx >= 0; idx = g_wc[idx].next) {
        WcQuad *q = &g_wc[idx];
        float dx = q->wx[0] - w[0][0], dy = q->wy[0] - w[0][1],
              dz = q->wz[0] - w[0][2];
        if (dx * dx + dy * dy + dz * dz > 1024.0f) continue;
        if (q->lastFrame != g_wcFrame) {
            if (q->seen < 1000) q->seen++;
            q->lastFrame = g_wcFrame;
        }
        g_wcHit++;
        return;                       /* already known, and drawn by the game */
    }
    if (g_wcN >= WC_MAX) {
        if (g_wcMatchRate < 50) wcReset();   /* it was never the city */
        return;
    }
    idx = g_wcN++;
    {
        WcQuad *q = &g_wc[idx];
        for (i = 0; i < 4; i++) {
            q->wx[i] = w[i][0]; q->wy[i] = w[i][1]; q->wz[i] = w[i][2];
            q->u[i] = qu[i]; q->v[i] = qv[i]; q->col[i] = cols[i];
        }
        q->layer = layer;
        q->seen = 1;
        q->lastFrame = g_wcFrame;
        q->next = g_wcHead[h];
        g_wcHead[h] = idx;
    }
}

/* draw everything the city has shown us that the game is not drawing now */
static void wcEmit(void)
{
    int i, k;
    g_wcDrawn = 0;
    g_wcLive = 0;
    if (!g_wcOn || !g_wc || !g_wcTrack) return;
    for (i = 0; i < g_wcN; i++) {
        WcQuad *q = &g_wc[i];
        float px[4], py[4], pz[4];
        int order[6] = { 0, 1, 2, 0, 2, 3 }, j;
        DWORD key;
        float zmin = 1e30f;
        if (q->seen < WC_KEEP) continue;
        g_wcLive++;
        if (q->lastFrame == g_wcFrame) continue;      /* the game has it */
        if (g_buildCount + 6 > MAX_QUADS * 6) break;
        for (k = 0; k < 4; k++) {
            float w[3] = { q->wx[k], q->wy[k], q->wz[k] }, g[3], o[3];
            xfApply(&g_camAcc, w, g);
            wcFromGame(g, o);
            px[k] = o[0]; py[k] = o[1]; pz[k] = o[2];
            if (-o[2] < zmin) zmin = -o[2];
        }
        if (zmin < 16.0f) continue;                   /* behind or on the eye */
        key = q->layer * 0x40000u + (DWORD)(zmin * 8.0f);
        if (g_buildCount / 6 < MAX_QUADS)
            g_quadKey[g_buildCount / 6] = (unsigned __int64)key + 16;
        for (j = 0; j < 6; j++) {
            k = order[j];
            g_build[g_buildCount].x = px[k];
            g_build[g_buildCount].y = py[k];
            g_build[g_buildCount].z = pz[k];
            g_build[g_buildCount].col = q->col[k];
            g_build[g_buildCount].u = q->u[k];
            g_build[g_buildCount].v = q->v[k];
            g_build[g_buildCount].d = 0.5f;
            g_buildCount++;
        }
        g_wcDrawn++;
    }
}

static int   g_hudFix = 1;   /* 0 all sprites world, 1 base-0 bank fixed, 2 all fixed */
/* ------------------------------------------------------------ sprite id sets
 * The overlay is a few dozen sprites and every one of them is a texture id
 * that never changes: the ammo drum is 1378..1397, CREDITS is 1506, the car
 * chase dashboard is 1603/1604 with its gauges on 1605..1607 and its labels
 * on 1619..1621. Naming them in the ini by id is therefore exact, needs no
 * heuristics about size or position, and can be changed while the game runs.
 * Written the way a person would: "1603-1609,1619-1623". */
#define IDR_MAX 8
typedef struct { unsigned lo, hi; } IdRange;
static int  cfgRanges(const char *key, IdRange *out, int max);
static IdRange g_hudHide[IDR_MAX];   static int g_hudHideN;   /* [view] hudhide  */
static IdRange g_panelIds[IDR_MAX];  static int g_panelIdsN;  /* [view] panelids */
static int  g_panelDist  = 110;      /* [view] paneldist, game units            */
static int  g_panelDrop  = 60;       /* [view] paneldrop, screen pixels down    */
static int  g_panelScale = 100;      /* [view] panelscale, percent              */
static int  g_hudLog;                /* [view] hudlog: name every overlay sprite */
static int  g_hudOwn;                /* [view] hudown: draw our own drum and lives */
static int  g_hudOwnSize = 100;      /* [view] hudownsize, percent                 */
static int  g_hudLives;              /* [view] hudlives: 0 badge, 1 pip, 2 hidden  */
static DWORD g_ammoId[2];            /* drum texture id seen this frame, per player */
static int  g_lifeN[2];              /* 1377 icons counted this frame, per player   */
static DWORD g_ammoIdS[2];           /* the same, held for the frame being drawn    */
static int  g_lifeNS[2];
static int idIn(const IdRange *r, int n, unsigned id)
{
    int i;
    for (i = 0; i < n; i++) if (id >= r[i].lo && id <= r[i].hi) return 1;
    return 0;
}

static int   g_hudSpread = 100;  /* [view] hudspread, percent from the centre   */
static int   g_hudScale  = 100;  /* [view] hudscale, percent                    */
static int   g_hideXhair = 1;/* 0 both, 1 P1 (+P2 in akimbo), 2 both, 3 P1 only */
extern int   g_akimboOn;
static int   g_pvFollow = 1; /* preview follows the game's own field of view    */
static int   g_pvZoom = 130; /* and magnifies it by this percent                */
static int   g_pvFull;       /* start the preview borderless full screen        */
static int   g_texLearn;                /* fall back to the colour vote      */
static int   g_clampDrop = 1;
static LONG  g_clampDropped;
/* corners the engine's projector (0x445BE0) clipped at the near plane: it
 * writes rhw = 0, depth key = 0 and sx = sy = 0, which after the centre
 * offset lands exactly on (cx, cy). Unprojected, such a corner sits on the
 * eye and the road quad it belongs to stretches across the view. The old
 * w == 0 check lived inside the truexyz branch, which is off with passes. */
static int   g_deepDrop = 0;   /* [view] deepdrop: drop pieces still straddling
                                * the eye plane at the split limit - what the
                                * engine itself does with them                */
static int   g_behindDrop = 0; /* [view] behinddrop: drop pieces wholly behind
                                * this pass's near plane                      */
static DWORD g_deepDropped, g_deepDroppedS, g_behindDropped, g_behindDroppedS;
static int   g_nearDrop = 1;                  /* [view] neardrop: 0 off, 1 drop (engine behaviour), 2 repair (experimental, flickers on long strips) */
static LONG  g_nearDropped, g_nearW0, g_nearRhw0, g_nearCentre, g_nearRep1, g_nearRep2;
/* the ground around the player is tessellated differently by every pass
 * (each subdivides near its own camera) and the pieces never dedup, so they
 * pile up as shards of asphalt at different texture scales. Inside nearown
 * units of the eye only one pass may draw: the native pass ahead of the eye
 * (z < 0), the back pass behind it; the other passes stay out. */
static float g_nearOwn = 800.0f;              /* [view] nearown, game units */
static LONG  g_nearOwnSkip;

/* Radial distance into a layer's 18 bits. It used to be distance * 8, capped
 * at the top of the slot: everything past 32767 units - 244 m, which is most
 * of a city street - came out with the SAME depth. The layer's own painting
 * order still separated whole quads, but the depth buffer could no longer
 * tell one distant building from another, and where two of them overlapped
 * the winner was decided by rasterisation. That decision is not the same for
 * the left eye and the right, so the two eyes were shown different buildings
 * in the same place, and there is nothing the eyes can do with that but
 * strain. (It stayed hidden while the far corners were being clamped to
 * 32767 anyway; exact geometry is what put real distances in.)
 *
 * So: a curve that never saturates. d/(d + RAD_C) rises to 1 and never
 * reaches it, keeps about 30 steps per unit close up, and still has
 * thousands of steps between 300 m and 500 m. It is monotonic in distance,
 * so the painting order is exactly what it was. */
#define RAD_C 8000.0f
static DWORD radialKey(float d)
{
    float f;
    if (d < 0.0f) d = 0.0f;
    f = (float)(LAYER - 1) * (d / (d + RAD_C));
    return (DWORD)f;
}

/* ---- exact geometry (see the clipper detour below pushQuad) ----
 * A quad whose four corners are the engine's own view-space vertices - from
 * the projector hook (all four hit) or handed in by the clipper detour - is
 * EXACT: no unprojection, no near plane, no +-10000 clamp, no far sentinel.
 * Such a quad is not resolved by direction or by fuzzy centroid; it is a
 * polygon the engine walked, and the first pass to walk it draws all of it.
 * g_ex* is the clipper detour's input to pushQuad: corners in the pass's own
 * view space (x right, y down, z forward) plus the (s,t) of each corner
 * inside the parent polygon, for the texture and the vertex shades. */
static int      g_trueClip = 1;               /* [view] trueclip */
static int      g_splitDepth = 0x20;          /* [view] splitdepth: as the engine, 0x20 */
static int      g_exOn;                       /* pushQuad: take g_exXyz/g_exST */
static float    g_exXyz[4][3], g_exST[4][2];
static DWORD    g_exDup, g_exDupS, g_exQuads, g_exQuadsS, g_exFull, g_exFullS;
static DWORD    g_exSeenN, g_exSeenNS;
/* quads that still reach VR the old way (unprojected screen corners), split
 * by layer: the layer says which object type submitted them - type 0 goes
 * through 0x00442560, types 1..3 through 0x00443CC0 and the clipper, and the
 * layers are [0x004CF228] + type * 4. If the floor is still wrong, this line
 * says whether it is even coming through a path this build touches. */
static DWORD    g_legacyQ, g_legacyQS, g_legacyL[16], g_legacyLS[16];
static DWORD    g_clipPoly, g_clipPolyS, g_clipNoRec, g_clipNoRecS, g_clipPieces, g_clipPiecesS,
                g_clipHeld, g_clipHeldS, g_clipDeep, g_clipDeepS, g_clipDup, g_clipDupS;
static int exactSeen(DWORD tex, DWORD layer, const float *px, const float *py, const float *pz);
#define EXS_N    32768
#define EXS_HEAD 8192
typedef struct { float k[12]; DWORD tex, layer; int next; } ExsEnt;
static ExsEnt  *g_exs;
static int      g_exsN;
static int      g_exsHead[EXS_HEAD];
static void exactClear(void);
static DWORD    g_clipRec[27];         /* the first engine piece's record */
static int      g_clipRecOk;
static DWORD    g_clipEmit;
#define TOPQ 3
typedef struct { DWORD tex, flags, from; float sx[4], sy[4]; DWORD w[4]; } TopQuad;
static TopQuad g_top[TOPQ];
static float   g_topW[TOPQ];
static float g_wideMax;
static DWORD g_wideTex, g_wideFlags, g_wideFrom, g_quadRa;
static DWORD g_spqHit, g_spqMiss;

/* Ray from the eye through screen point (mx,my), against every world
 * triangle already in this frame's buffer (d in (0,1)). Returns the distance
 * along -Z of the nearest hit, or -1. */
static float rayDepth(float mx, float my)
{
    float dx = (mx - g_cx) / g_fx, dy = -(my - g_cy) / g_fy, dz = -1.0f;
    float best = 1e30f;
    UINT i2;
    for (i2 = 0; i2 + 2 < g_buildCount; i2 += 3) {
        const Vtx *a = &g_build[i2], *b = &g_build[i2 + 1], *c = &g_build[i2 + 2];
        float e1x, e1y, e1z, e2x, e2y, e2z, px2, py2, pz2, det, inv, u, v, t, qx, qy, qz;
        if (a->d >= 1.0f || a->d <= 0.0f) continue;
        e1x = b->x - a->x; e1y = b->y - a->y; e1z = b->z - a->z;
        e2x = c->x - a->x; e2y = c->y - a->y; e2z = c->z - a->z;
        px2 = dy * e2z - dz * e2y; py2 = dz * e2x - dx * e2z; pz2 = dx * e2y - dy * e2x;
        det = e1x * px2 + e1y * py2 + e1z * pz2;
        if (det > -1e-7f && det < 1e-7f) continue;
        inv = 1.0f / det;
        u = (-a->x * px2 - a->y * py2 - a->z * pz2) * inv;
        if (u < 0.0f || u > 1.0f) continue;
        qx = -a->y * e1z + a->z * e1y; qy = -a->z * e1x + a->x * e1z; qz = -a->x * e1y + a->y * e1x;
        v = (dx * qx + dy * qy + dz * qz) * inv;
        if (v < 0.0f || u + v > 1.0f) continue;
        t = (e2x * qx + e2y * qy + e2z * qz) * inv;
        if (t > 16.0f && t < best) best = t;
    }
    return best < 1e29f ? best : -1.0f;
}

/* ------------------------------------------------- autofar: backdrops by motion
 *
 * The engine's depth word saturates at 245 m, so a skyline is modelled small
 * and hung near the camera. farlayers tried to name such things by sort layer
 * and could not: stage 1 keeps its skyline in layer 3, stage 2 keeps the ship
 * there. The layer is authoring convention; the MOTION is physics.
 *
 * When the camera translates, every world-fixed point moves in view space by
 * the same vector - minus the camera's displacement - whatever its distance:
 * a kerb at two metres and a tower at two hundred both shift by exactly the
 * metre the camera drove. A thing attached to the camera shifts by nothing.
 * So, per texture id, the mean view-space centroid of its quads is kept in a
 * ring of snapshots; between two snapshots with the same camera heading
 * (rotation would move everything, and is simply not used) the median shift
 * over all textures IS the camera's own displacement in view units, and a
 * texture whose shift is a small fraction of that median while the median is
 * large has been riding along. Once a texture has said so a few times and
 * never the opposite, and it sits beyond autofarmin metres, its quads are
 * scaled about the eye by farscale, as farlayers did: every corner stays on
 * its ray, the picture and the laser do not move, only the stereo does. The
 * sort key is untouched, so visibility is still the engine's.
 *
 * The camera position is the engine's own, 0x004DB898/9C/A0 - the same three
 * floats its per-object reject reads - and its heading the words at
 * 0x004DB894 (yaw) and 0x004DB892 (pitch). The log line says what was seen:
 * "autofar cam x y z yaw p | med N | far: tex d(m) y/n ..." */
#define AF_TEX  4096
#define AF_SNAP 12
#define AF_LIST 24
typedef struct { float sx, sy, sz; DWORD n; } AfAcc;
typedef struct { DWORD tick; float cam[3]; short yaw, pitch; int valid;
                 float c[AF_TEX][3]; unsigned char have[AF_TEX]; } AfSnap;
static AfAcc   g_afAcc[AF_TEX];
static AfSnap  g_afSnap[AF_SNAP];
static int     g_afHead;
static unsigned char g_afYes[AF_TEX], g_afNo[AF_TEX];
static signed char   g_afState[AF_TEX];        /* 1 attached, -1 fixed, 0 unknown */
static float   g_afDist[AF_TEX];               /* last mean distance, metres */
static int     g_autoFar = 1;                  /* [view] autofar */
static int     g_afMin   = 15;                 /* [view] autofarmin, metres */
static int     g_afRatio = 20;                 /* [view] autofarratio, percent of the median */
static float   g_afMedS, g_afCamS[3];
static int     g_afYawS, g_afPitchS, g_afCamOk, g_afPairs, g_afPairsS, g_afApplied, g_afAppliedS;
static float   g_afDelta[AF_TEX];

static int __cdecl afCmpF(const void *a, const void *b)
{
    float x = *(const float *)a, y = *(const float *)b;
    return (x > y) - (x < y);
}

static void afFrame(void)
{
    BYTE *base = (BYTE *)GetModuleHandleA(NULL);
    DWORD now = GetTickCount();
    AfSnap *s;
    int i, k, best = -1;
    if (!g_autoFar || !base) {
        for (i = 0; i < AF_TEX; i++) g_afAcc[i].n = 0;
        return;
    }
    s = &g_afSnap[g_afHead];
    if (s->valid && now - s->tick < 250) return;  /* keep accumulating; four snapshots a second */
    g_afHead = (g_afHead + 1) % AF_SNAP;
    s = &g_afSnap[g_afHead];
    s->tick = now;
    s->valid = 0;
    if (!IsBadReadPtr(base + 0xDB892, 16)) {
        s->cam[0] = *(float *)(base + 0xDB898);
        s->cam[1] = *(float *)(base + 0xDB89C);
        s->cam[2] = *(float *)(base + 0xDB8A0);
        s->yaw    = *(short *)(base + 0xDB894);
        s->pitch  = *(short *)(base + 0xDB892);
        s->valid  = 1;
        g_afCamOk = 1;
        g_afCamS[0] = s->cam[0]; g_afCamS[1] = s->cam[1]; g_afCamS[2] = s->cam[2];
        g_afYawS = s->yaw; g_afPitchS = s->pitch;
    }
    for (i = 0; i < AF_TEX; i++) {
        AfAcc *a = &g_afAcc[i];
        if (a->n) {
            s->c[i][0] = a->sx / a->n; s->c[i][1] = a->sy / a->n; s->c[i][2] = a->sz / a->n;
            s->have[i] = 1;
            g_afDist[i] = (float)sqrt((double)(s->c[i][0]*s->c[i][0] + s->c[i][1]*s->c[i][1] +
                                               s->c[i][2]*s->c[i][2])) / g_unitsPerMetre;
        } else {
            s->have[i] = 0;
        }
        a->n = 0; a->sx = a->sy = a->sz = 0.0f;
    }
    if (!s->valid) return;
    /* the oldest snapshot, up to three seconds back, with the same heading */
    for (k = 1; k < AF_SNAP; k++) {
        AfSnap *o = &g_afSnap[(g_afHead + AF_SNAP - k) % AF_SNAP];
        int dy, dp;
        if (!o->valid || now - o->tick > 3000) break;
        dy = (int)(short)(o->yaw - s->yaw); dp = (int)(short)(o->pitch - s->pitch);
        if (dy < 0) dy = -dy; if (dp < 0) dp = -dp;
        if (dy > 0x5B || dp > 0x5B) break;          /* half a degree of 0xB6 */
        if (now - o->tick >= 400) best = (g_afHead + AF_SNAP - k) % AF_SNAP;
    }
    if (best < 0) return;
    {
        AfSnap *o = &g_afSnap[best];
        int n = 0;
        float med;
        for (i = 0; i < AF_TEX; i++) {
            float dx, dy2, dz;
            if (!s->have[i] || !o->have[i]) { g_afDelta[i] = -1.0f; continue; }
            dx = s->c[i][0] - o->c[i][0]; dy2 = s->c[i][1] - o->c[i][1]; dz = s->c[i][2] - o->c[i][2];
            g_afDelta[i] = (float)sqrt((double)(dx*dx + dy2*dy2 + dz*dz));
            n++;
        }
        if (n < 8) return;
        {
            static float tmp[AF_TEX];
            int m = 0;
            for (i = 0; i < AF_TEX; i++) if (g_afDelta[i] >= 0.0f) tmp[m++] = g_afDelta[i];
            qsort(tmp, m, sizeof(float), afCmpF);
            med = tmp[m / 2];
        }
        g_afMedS = med / g_unitsPerMetre;
        if (med < 0.5f * g_unitsPerMetre) return;   /* the camera has to have moved */
        g_afPairs++;
        for (i = 0; i < AF_TEX; i++) {
            if (g_afDelta[i] < 0.0f) continue;
            if (g_afDelta[i] < med * (float)g_afRatio / 100.0f) {
                if (g_afYes[i] < 250) g_afYes[i]++;
            } else {
                if (g_afNo[i] < 250) g_afNo[i]++;
            }
            if (g_afYes[i] >= 3 && g_afYes[i] >= 4 * g_afNo[i]) g_afState[i] = 1;
            else if (g_afNo[i] >= 2 && g_afNo[i] > g_afYes[i]) g_afState[i] = -1;
        }
    }
}

static int afLogLine(char *p)
{
    int i, listed = 0;
    char *p0 = p;
    p += wsprintfA(p, "autofar %d cam %d %d %d yaw %d pitch %d | med %d.%dm pairs %u applied %u | far:",
                   g_autoFar, (int)g_afCamS[0], (int)g_afCamS[1], (int)g_afCamS[2],
                   g_afYawS, g_afPitchS, (int)g_afMedS, (int)(g_afMedS * 10.0f) % 10,
                   g_afPairsS, g_afAppliedS);
    for (i = 0; i < AF_TEX && listed < AF_LIST; i++)
        if (g_afState[i] == 1) {
            p += wsprintfA(p, " t%d %dm %u/%u", i, (int)g_afDist[i], g_afYes[i], g_afNo[i]);
            listed++;
        }
    p += wsprintfA(p, " | leaning:");
    for (i = 0; i < AF_TEX && listed < AF_LIST + 8; i++)
        if (g_afState[i] == 0 && g_afYes[i] > 0) {
            p += wsprintfA(p, " t%d %dm %u/%u", i, (int)g_afDist[i], g_afYes[i], g_afNo[i]);
            listed++;
        }
    p += wsprintfA(p, "\r\n");
    return (int)(p - p0);
}

static void pushQuad(const DWORD *q)
{
    float px[4], py[4], pz[4];
    DWORD layer, col, key;
    int i, order[6] = { 0, 1, 2, 0, 2, 3 };
    const TexReg *tr = NULL;
    float qu[4], qv[4];
    int sh[3], base[3], vx[4], flat = 0;
    int trueN = 0, behind = 0, radial = 0;
    int nearMask = 0;                     /* corners the engine near-clipped */
    DWORD vcol[4], wrad[4];

    if (g_buildCount + 6 > MAX_QUADS * 6) return;
    layer = q[6] / LAYER;
    if (layer == 3 && g_skip3 == 1) return;   /* emergency ini switch only */

    /* Which quads exist at all, and how they are coloured, is decided by the
     * low three bits of flags through the tables at 0x10010188 (bit 24 clear)
     * and 0x100101A8 (bit 24 set). Most entries point at a bare "ret": those
     * quads are silently dropped by the engine, and drawing them was what put
     * the pale panels over the city. Variant 4 (0x100048E0) is an UNTEXTURED
     * polygon whose colour is the id field read as 5-5-5, low bits red. */
    {
        int var = (int)(q[0] & 7);
        if (q[0] & 0x1000000) {
            if (var != 2 && var != 4) { g_dropVar++; return; }
        } else {
            if (var != 1 && var != 2 && var != 4) { g_dropVar++; return; }
        }
        flat = (var == 4);
    }

    /* the texture decides whether this quad exists at all: HGL_D3D 0x10005178
     * returns straight away when the slot holds a dynamic texture (d3 bit 2) -
     * those are drawn by the sprite slot, never as quads. */
    /* Which texture a quad wears used to be decided by a colour vote against
     * the captured screen, because the comment above this file's texture
     * section was still true: "quad.texture should equal base + slot - that
     * equation is the one thing not yet confirmed on a live run". It is
     * confirmed now. Every probe since reports "miss 0..0": regFind(q[1])
     * resolves EVERY id in the frame, without exception.
     * The vote, meanwhile, is written once into g_learn and never revised, so
     * a single early mistake sticks for the whole session - which is how a
     * road sign ended up painted across the pavement and stayed there even
     * with cityahead at 0. Direct lookup first; the vote only if asked for. */
    if (flat) tr = NULL;
    else if (g_doTex) {
        tr = regFind(q[1]);
        if (!tr && g_texLearn && q[1] < LEARN_MAX && g_learn[q[1]] >= 0 &&
            g_reg[g_learn[q[1]]].used)
            tr = &g_reg[g_learn[q[1]]];
    }
    if (tr && (tr->d3 & 4)) { g_dropDyn++; return; }
    if (flat) {
        /* nothing to look up */
    } else if (tr) {
        if (q[1] < g_idHitMin) g_idHitMin = q[1];
        if (q[1] > g_idHitMax) g_idHitMax = q[1];
    } else {
        if (q[1] < g_idMissMin) g_idMissMin = q[1];
        if (q[1] > g_idMissMax) g_idMissMax = q[1];
    }

    /* painter key, HGL_D3D 0x100055F6: bits 10-11 of flags choose min, max or
     * mean of the four w, or "one below the previous quad" for decals. The
     * frame is then radix sorted and drawn from the largest key down. */
    {
        DWORD w0 = q[6], w1 = q[10], w2 = q[14], w3 = q[18];
        switch ((q[0] >> 10) & 3) {
        case 0:
            key = w0;
            if (w1 < key) key = w1;
            if (w2 < key) key = w2;
            if (w3 < key) key = w3;
            break;
        case 1:
            key = w0;
            if (w1 > key) key = w1;
            if (w2 > key) key = w2;
            if (w3 > key) key = w3;
            break;
        case 2:
            key = (DWORD)(((unsigned __int64)w0 + w1 + w2 + w3) >> 2);
            break;
        default:
            key = g_prevKey - 1;
            break;
        }
        g_prevKey = key;
    }

    /* ------------------------------------------------------ saturated quads
     * HGL_D3D clamps every projected coordinate to +-10000 (0x00445CA0, the
     * constants 0x461C4000 and 0xC61C4000). A vertex that ends up just in
     * front of the eye divides by a near-zero w, blows past that limit and
     * arrives here pinned to exactly 10000 - a number that no longer means
     * anything. The game's own rasteriser does not care, it just fills to the
     * edge of the screen. We do care: unprojecting a saturated coordinate
     * puts the vertex kilometres sideways and paints a stripe across the
     * whole view. That is the artefact that shows up when firing, when
     * something passes close to the muzzle.
     * The widest quad the probe ever caught was exactly 10000 px wide,
     * texture 1777, submitted from 0x00443C51 inside 0x00442960 - the clipped
     * polygon path. Saturated means unusable, so drop it. */
    /* The clamp is applied to the OFFSET from the screen centre, not to the
     * final coordinate: 0x00445CD4 writes word[0x004CF80A] + clamp(x*fx/z),
     * so a saturated vertex arrives as 320 - 10000 = -9680 on the left and
     * 320 + 10000 = 10320 on the right. Testing the raw coordinate against
     * +-9990 therefore caught every saturated vertex on the right and NOT ONE
     * on the left, which is exactly the lopsided flicker that survived the
     * last fix. The probe says it plainly: the three widest quads all have a
     * corner at sx -9680 and all three sailed through. Test the offset. */
    /* Ask the projection hook what these four corners really were. A hit is
     * the engine's own view space vertex; a miss falls back to unprojecting
     * the screen record exactly as before, so with truexyz = 0 - and for
     * sprites and clipper output the hook never saw - nothing changes. */
    if (g_exOn) {
        int w0c = 0;
        for (i = 0; i < 4; i++) {
            px[i] =  g_exXyz[i][0];
            py[i] = -g_exXyz[i][1];
            pz[i] = -g_exXyz[i][2];
            /* near-plane clamp: the engine zeroes the DEPTH bits, not the whole
             * word - a layer-N vertex is N*LAYER + 0. Testing the full DWORD
             * == 0 only ever matched layer 0, which is why the L14 water card
             * (14*LAYER, depth 0) slipped every previous drop. Mask the layer. */
            if ((q[6 + i * 4] % LAYER) == 0) w0c++;
        }
        trueN = 4;
        /* the blue water card also arrives here, as a clipper piece (aimprobe:
         * tex 1842, ra 0x443C51, engine "0 0 0 0", ours 1-6 m). All four
         * corners nearer than the engine's near plane AND reconstructed right
         * in front of the eye and very close: the near zone the engine clips
         * away, stretched into a card. Behind-you 360 geometry also has w == 0
         * but reconstructs BEHIND (centre z > 0) or far, so the front+near gate
         * spares it. */
        if (g_nearDropX && w0c == 4) {
            float cz = (pz[0]+pz[1]+pz[2]+pz[3]) * 0.25f;
            float cx3 = (px[0]+px[1]+px[2]+px[3]) * 0.25f;
            float cy3 = (py[0]+py[1]+py[2]+py[3]) * 0.25f;
            /* near (within ~11 m), any direction: the plate hangs DOWN, not
             * forward, so a "front only" gate missed it. The 360 world's
             * behind-you geometry reconstructs FAR, so a near gate spares it. */
            if (cx3*cx3 + cy3*cy3 + cz*cz < 1500.0f*1500.0f) {
                g_nearCardDrop++; return;
            }
        }
    } else if (g_trueXyz) {
        int w0count = 0;
        int w0dep = 0;          /* corners with DEPTH bits zero (near-plane clamp) */
        for (i = 0; i < 4; i++) {
            const DWORD *tv = txGet(&q[3 + i * 4]);
            if (tv) {
                px[i] =  *(const float *)&tv[0];
                py[i] = -*(const float *)&tv[1];  /* game y down, ours up      */
                pz[i] = -*(const float *)&tv[2];  /* game z forward, ours back */
                /* Verify the hit against the corner's own unprojection. The
                 * exact cache is keyed on the projected record {sx,sy,extra,w};
                 * for a far vertex the engine writes a SATURATED depth word, so
                 * many distinct points share one record and a lookup returns
                 * whichever was stored last. Live at the quay this made sea
                 * quads (t1842) in the rotated passes pick up the monorail
                 * deck's corners - two of four corners jumping +1793 in y - the
                 * asphalt wedges into the sky. The cure is cheap: for a corner
                 * whose record is HONEST (in front of the near plane, not
                 * clamped, not the dead centre) the unprojection is accurate,
                 * so if the cached point sits far from it the hit is a
                 * collision and the unprojection is the truth. Near-plane and
                 * clamped corners keep the exact value - that is the whole
                 * reason the cache exists, and unproject cannot serve them. */
                {
                    DWORD wi = q[6 + i * 4];
                    float sxi = *(float *)&q[3 + i * 4];
                    float syi = *(float *)&q[4 + i * 4];
                    float vx = sxi - g_cx, vy = syi - g_cy;
                    int honest = (wi != 0) &&
                                 vx > -9990.0f && vx < 9990.0f &&
                                 vy > -9990.0f && vy < 9990.0f &&
                                 !(sxi == g_cx && syi == g_cy);
                    if (honest) {
                        float ux, uy, uz, dx, dy, dz;
                        unproject(sxi, syi, wi, &ux, &uy, &uz);
                        dx = px[i] - ux; dy = py[i] - uy; dz = pz[i] - uz;
                        if (dx*dx + dy*dy + dz*dz > (300.0f * 300.0f)) {
                            px[i] = ux; py[i] = uy; pz[i] = uz;
                            g_txBadHit++;
                        }
                    }
                    /* resolved either way - keep the quad on the exact path */
                    trueN++;
                }
            }
            if (q[6 + i * 4] == 0) { behind = 1; w0count++; }  /* w==0: near plane */
            /* depth bits zero regardless of layer - the real near-plane clamp.
             * Layer 0 makes this identical to w==0; a layer-N card (the L14
             * water plate) is caught here where the full-word test missed it. */
            if ((q[6 + i * 4] % LAYER) == 0) w0dep++;
        }
        g_txHit += (DWORD)trueN;
        g_txMiss += (DWORD)(4 - trueN);
        if (behind && trueN < 4) return;          /* nothing usable to draw */

        /* The blue water card. aimprobe named it: tex 1842, true4, engine
         * "0 0 0 0" - ALL FOUR corners nearer than the engine's near plane -
         * with a screen box running from the dead centre (320,240) out to the
         * +-10000 clamp, reconstructed 1-6 m across the whole lower view. A
         * quad entirely in front of the near plane is exactly what the engine
         * itself deletes (behind = 0 keeps none), but the projector hook
         * captures it whole and the exact path draws it, because trueN == 4
         * skips every near-plane guard. It cannot be real geometry: nothing
         * visible is wholly nearer than the near plane. The ground under the
         * feet has real depth (w != 0) and is untouched; the 360 world is
         * rebuilt by the rotated passes, not by this stretched card. Drop it.
         * neardropx = 0 keeps the old behaviour, live. */
        if (g_nearDropX && w0dep == 4) {
            float cz = (pz[0]+pz[1]+pz[2]+pz[3]) * 0.25f;
            float cx3 = (px[0]+px[1]+px[2]+px[3]) * 0.25f;
            float cy3 = (py[0]+py[1]+py[2]+py[3]) * 0.25f;
            /* near (~11m) any direction: plate hangs DOWN not forward */
            if (cx3*cx3 + cy3*cy3 + cz*cz < 1500.0f*1500.0f) {
                g_nearCardDrop++; return;
            }
        }

        /* Planarity guard for the rotated passes. The wedges are not a
         * reconstruction error - exact xyz and unprojection AGREE on every
         * corner (badhit stayed 0). The quad ITSELF is corrupt: in a rotated
         * pass the engine handed pushQuad a "sea" quad (t1842) whose four
         * corner records mix two sea vertices with two monorail-deck vertices
         * 1793 units higher, so it reconstructs faithfully as a flap bent
         * ninety degrees - the asphalt fanning into the sky. A real quad from
         * this engine is planar; a mix of two objects' corners is not. Drop a
         * rotated-pass quad whose fourth corner lies far off the plane of the
         * other three. The native pass draws the real flat sea in the same
         * place and groundfill backs it, so nothing is lost. Never touches the
         * native pass (g_pass == 0) - only the six rotated ones can stitch
         * across objects like this. */
        if (g_pass && trueN == 4) {
            float e1x = px[1]-px[0], e1y = py[1]-py[0], e1z = pz[1]-pz[0];
            float e2x = px[2]-px[0], e2y = py[2]-py[0], e2z = pz[2]-pz[0];
            float nx = e1y*e2z - e1z*e2y;
            float ny = e1z*e2x - e1x*e2z;
            float nz = e1x*e2y - e1y*e2x;
            float nl = (float)sqrt((double)(nx*nx + ny*ny + nz*nz));
            if (nl > 1e-3f) {
                float d = (nx*(px[3]-px[0]) + ny*(py[3]-py[0]) +
                           nz*(pz[3]-pz[0])) / nl;
                if (d < 0.0f) d = -d;
                if (d > 700.0f) { g_bentDrop++; return; }
            }
        }
    }

    if (trueN < 4) { g_legacyQ++; g_legacyL[layer & 15]++; }

    /* The +-10000 clamp only matters for a corner that has to be unprojected;
     * one that came back from the hook is exact however far off screen the
     * engine pinned it. That is the muzzle flicker gone, for free. */
    if (trueN < 4) {
        int bad = 0;
        for (i = 0; i < 4; i++) {
            float sxi = *(float *)&q[3 + i * 4], syi = *(float *)&q[4 + i * 4];
            float rhw = *(float *)&q[5 + i * 4];
            int w0 = (q[6 + i * 4] == 0), r0 = (rhw == 0.0f);
            int ce = (sxi == g_cx && syi == g_cy);
            if (w0) InterlockedIncrement(&g_nearW0);
            if (r0) InterlockedIncrement(&g_nearRhw0);
            if (ce) InterlockedIncrement(&g_nearCentre);
            if (w0 || r0 || ce) { bad++; nearMask |= 1 << i; }
        }
        if (bad && g_nearDrop == 1) { InterlockedIncrement(&g_nearDropped); return; }
        if (bad && g_nearDrop == 2 && bad >= 3) { InterlockedIncrement(&g_nearDropped); return; }
        if (g_nearDrop != 2) nearMask = 0;
    }
    if (g_clampDrop && trueN < 4) {
        for (i = 0; i < 4; i++) {
            float vx = *(float *)&q[3 + i * 4] - g_cx;
            float vy = *(float *)&q[4 + i * 4] - g_cy;
            if (vx <= -9990.0f || vx >= 9990.0f ||
                vy <= -9990.0f || vy >= 9990.0f) {
                g_clampDropped++;
                return;
            }
        }
    }
    {   /* Three widest quads of the session with every corner written out.
         * "Enemy meshes flicker at the edges when firing" is still unexplained
         * and the last guess - saturated coordinates - was only part of it:
         * the worst quad now measures 9513 px, under the 10000 clamp, so it
         * was never saturated at all. Guessing again would be a waste of a
         * run, so record the shape instead: corners, depths, submitter. */
        float lo2 = 1e9f, hi2 = -1e9f;
        for (i = 0; i < 4; i++) {
            float v = *(float *)&q[3 + i * 4];
            if (v < lo2) lo2 = v;
            if (v > hi2) hi2 = v;
        }
        if (hi2 - lo2 > g_topW[TOPQ - 1]) {
            int slot2 = TOPQ - 1, m2;
            for (m2 = 0; m2 < TOPQ - 1; m2++)
                if (hi2 - lo2 > g_topW[m2]) { slot2 = m2; break; }
            for (m2 = TOPQ - 1; m2 > slot2; m2--) g_top[m2] = g_top[m2 - 1],
                                                  g_topW[m2] = g_topW[m2 - 1];
            g_topW[slot2] = hi2 - lo2;
            g_top[slot2].tex = q[1];
            g_top[slot2].flags = q[0];
            g_top[slot2].from = g_quadRa;
            for (m2 = 0; m2 < 4; m2++) {
                g_top[slot2].sx[m2] = *(float *)&q[3 + m2 * 4];
                g_top[slot2].sy[m2] = *(float *)&q[4 + m2 * 4];
                g_top[slot2].w[m2]  = q[6 + m2 * 4];
            }
        }
    }
    {   /* the ugliest quad of the whole session, kept so that an artefact
         * nobody can catch with a key press still leaves evidence behind */
        float lo = 1e9f, hi = -1e9f;
        for (i = 0; i < 4; i++) {
            float v = *(float *)&q[3 + i * 4];
            if (v < lo) lo = v;
            if (v > hi) hi = v;
        }
        if (hi - lo > g_wideMax) {
            g_wideMax = hi - lo;
            g_wideTex = q[1];
            g_wideFlags = q[0];
            g_wideFrom = g_quadRa;
        }
    }
    for (i = 0; i < 4; i++) {
        float sxi = *(float *)&q[3 + i * 4];
        float syi = *(float *)&q[4 + i * 4];
        if (!behind) {
            if (sxi < g_sxMin) g_sxMin = sxi;
            if (sxi > g_sxMax) g_sxMax = sxi;
            if (syi < g_syMin) g_syMin = syi;
            if (syi > g_syMax) g_syMax = syi;
        }
        if (trueN < 4 && !(g_trueXyz && txGet(&q[3 + i * 4])))
            unproject(sxi, syi, q[6 + i * 4], &px[i], &py[i], &pz[i]);
    }
    if (nearMask) {
        /* corners already run round the outline: the UV table gives them
         * (0,0) (1,0) (1,1) (0,1); "strip 0,1,3,2" is only the emission
         * order. A near-clipped corner's record holds just (cx, cy), so its
         * position is rebuilt from the corners the engine did project.
         * Eye = origin of this space. */
        static const int cyc[4] = { 0, 1, 2, 3 };
        int nb = 0, bc[2], c;
        for (c = 0; c < 4; c++) if (nearMask & (1 << cyc[c])) { if (nb < 2) bc[nb] = c; nb++; }
        if (nb == 1) {
            int v = cyc[bc[0]], prev = cyc[(bc[0] + 3) & 3], next = cyc[(bc[0] + 1) & 3], opp = cyc[(bc[0] + 2) & 3];
            px[v] = px[prev] + px[next] - px[opp];
            py[v] = py[prev] + py[next] - py[opp];
            pz[v] = pz[prev] + pz[next] - pz[opp];
            InterlockedIncrement(&g_nearRep1);
        } else if (nb == 2 && ((bc[1] - bc[0]) & 3) != 2) {
            /* an edge is behind the eye: keep the visible edge and push the
             * other one out behind the eye along the ground, same plane */
            float mx = 0, mz = 0, len, L; int g0 = -1, g1 = -1;
            for (c = 0; c < 4; c++) if (!(nearMask & (1 << cyc[c]))) { if (g0 < 0) g0 = c; else g1 = c; }
            mx = (px[cyc[g0]] + px[cyc[g1]]) * 0.5f; mz = (pz[cyc[g0]] + pz[cyc[g1]]) * 0.5f;
            len = (float)sqrt((double)(mx * mx + mz * mz));
            if (len < 1.0f) { InterlockedIncrement(&g_nearDropped); return; }
            L = len + 150.0f;                          /* ~1 m past the eye */
            mx /= len; mz /= len;
            for (c = 0; c < 2; c++) {
                int cb = bc[c], v = cyc[cb], n1 = (cb + 1) & 3, n0 = (cb + 3) & 3;
                int g = (nearMask & (1 << cyc[n1])) ? cyc[n0] : cyc[n1];   /* the good neighbour */
                px[v] = px[g] - mx * L; py[v] = py[g]; pz[v] = pz[g] - mz * L;
            }
            InterlockedIncrement(&g_nearRep2);
        } else {
            InterlockedIncrement(&g_nearDropped); return;   /* diagonal pair */
        }
    }

    /* cube passes: unrotate, keep in one pass only, depth from radius */
    if (g_passOn && !g_inWorld && !g_pass) {
        int k;
        g_nonWorldQ++;
        {   /* [probe] transient non-world quad: id not seen for 400 ms */
            DWORD now = GetTickCount(), id = q[1] & 4095;
            if (now - g_fireTick < 300 && now - g_nnSeen[id] > 400) {
                LONG w = (InterlockedIncrement(&g_nnW) - 1) % 16;
                float x0 = 1e9f, y0 = 1e9f, x1 = -1e9f, y1 = -1e9f; int j;
                for (j = 0; j < 4; j++) {
                    float sx = *(float *)&q[3 + j * 4], sy = *(float *)&q[4 + j * 4];
                    if (sx < x0) x0 = sx; if (sx > x1) x1 = sx; if (sy < y0) y0 = sy; if (sy > y1) y1 = sy;
                }
                g_nnS++; g_nnR[w].id = q[1]; g_nnR[w].w = q[6]; g_nnR[w].ra = g_quadRa;
                g_nnR[w].cx = (int)((x0 + x1) * 0.5f); g_nnR[w].cy = (int)((y0 + y1) * 0.5f);
                g_nnR[w].wd = (int)(x1 - x0); g_nnR[w].ht = (int)(y1 - y0); g_nnR[w].dt = (int)(now - g_fireTick); g_nnR[w].xx = g_share ? (int)g_share->aim_x : -1; g_nnR[w].xy = g_share ? (int)g_share->aim_y : -1;
            }
            g_nnSeen[id] = now;
        }
        for (k = 0; k < g_nwN; k++) if (g_nwRa[k] == g_quadRa) { g_nwRaN[k]++; break; }
        if (k == g_nwN && g_nwN < 6) { g_nwRa[g_nwN] = g_quadRa; g_nwRaN[g_nwN] = 1; g_nwN++; }
    }
    if (g_passOn && g_camState == 1 && (g_inWorld || g_pass) && !behind) {
        int dir = (g_pass >= 1 && g_pass <= 5) ? (int)g_pass : 0;
        int slot = (int)g_pass & 7;
        g_passSeen[slot]++;
        {
            float rsx[4], rsy[4], rw[4];
            float bpx[4], bpy[4], bpz[4];
            int j;
            for (j = 0; j < 4; j++) {
                rsx[j] = *(float *)&q[3 + j * 4]; rsy[j] = *(float *)&q[4 + j * 4];
                rw[j] = (float)q[6 + j * 4];
                bpx[j] = px[j]; bpy[j] = py[j]; bpz[j] = pz[j];
            }
            if (g_passSeen[slot] == 1) {        /* first quad of this pass, this window */
                g_passFx[slot] = g_fx; g_passCx[slot] = g_cx;
                g_passFxSeen |= (1u << slot);
            }
            if (trueN == 4 && g_trueClip) {
                /* exact polygon: the first pass that walks it draws all of
                 * it, later passes drop it by identity. The native pass
                 * keeps its own duplicates (chunk seams), as the engine does.
                 * Pieces from the clipper detour were decided as a whole. */
                passUnrotate(dir, px, py, pz);
                if (!g_exOn && exactSeen(q[1], layer, px, py, pz) && g_pass) { g_exDup++; return; }
                g_exQuads++;
            } else if (g_passDedup) {
                passUnrotate(dir, px, py, pz);
                if (dir) {   /* [probe] centroid off the pass's own axis */
                    static const int axis6[6] = { 0, 1, 2, 3, 4, 5 };
                    float cx3 = 0, cy3 = 0, cz3 = 0, ax, ay, az; int d6, j2;
                    for (j2 = 0; j2 < 4; j2++) { cx3 += px[j2]; cy3 += py[j2]; cz3 += pz[j2]; }
                    ax = cx3 < 0 ? -cx3 : cx3; ay = cy3 < 0 ? -cy3 : cy3; az = cz3 < 0 ? -cz3 : cz3;
                    if (az >= ax && az >= ay) d6 = cz3 < 0 ? 0 : 1;
                    else if (ax >= ay)        d6 = cx3 < 0 ? 2 : 3;
                    else                      d6 = cy3 > 0 ? 4 : 5;
                    if (d6 != axis6[dir]) g_passOffAxis[slot]++;
                }
                if (g_nearOwn > 0) {
                    float cx3 = (px[0] + px[1] + px[2] + px[3]) * 0.25f;
                    float cz3 = (pz[0] + pz[1] + pz[2] + pz[3]) * 0.25f;
                    if (cx3 * cx3 + cz3 * cz3 < g_nearOwn * g_nearOwn) {
                        int owner = cz3 < 0 ? 0 : 1;
                        if (dir != owner) { InterlockedIncrement(&g_nearOwnSkip); return; }
                    }
                }
                if (pddSeen(q[1], px, py, pz, g_pass != 0, q[6])) return;
            } else if (!passResolve(dir, px, py, pz)) return;
            /* the alias wedge, judged in FINAL render space (post-unrotate):
             * a quad whose corners disagree in height by many metres. When it
             * comes from a flat remembered object the height is an alias and
             * the quad is dropped. Whatever the source, a tall survivor is
             * captured for the probe so the ones this does NOT drop can be
             * identified. */
            if (g_pass) {
                float hy = py[0], ly = py[0];
                int j3;
                for (j3 = 1; j3 < 4; j3++) {
                    if (py[j3] > hy) hy = py[j3];
                    if (py[j3] < ly) ly = py[j3];
                }
                /* A FLAT remembered object (its own game-space Y spans almost
                 * nothing) cannot have a quad in the sky. The earlier test
                 * looked for a big height SPREAD, which is only the EDGE of a
                 * wedge - the quads with one foot on the ground and one in the
                 * air. The body of the blade is quads with ALL FOUR corners
                 * aliased high: no spread, so they slipped through and the
                 * blade stayed. Judge by absolute height instead: for a flat
                 * object, ANY quad whose highest corner is well above where the
                 * object's own flat geometry can reach is an alias. skyhi is
                 * the ceiling, in render units. */
                if (g_wedgeFix && g_probeFlat && hy > (float)g_wedgeHi) {
                    g_wedgeDrop++;
                    return;
                }
                if (hy - ly > 900.0f) {
                    /* a tall quad we did NOT drop - record what it is */
                    g_wedgeSeen++;
                    g_wedgeTex = q[1];
                    g_wedgePass = (DWORD)g_pass;
                    g_wedgeObj = g_probeObj;
                    g_wedgeRaise = hy;
                    g_wedgeLow = ly;
                    g_wedgeObjYlo = g_probeObj ? g_probeYlo : 0.0f;
                    g_wedgeObjYhi = g_probeObj ? g_probeYhi : 0.0f;
                }
            }
            /* the far skyline blade. Not the rotated-pass alias - this one is
             * in the NATIVE pass, a low-detail distant backdrop the flat game
             * frames out at the edge of its 60-degree window and that VR (a
             * zoom especially) magnifies into a grey blade tilting into the
             * sky. Textures t1947 / t2029.. at 160 m, 26-36 m up. It is real
             * game geometry, so it is judged by geometry alone: a quad that is
             * BOTH high (a corner above skyhi game units) AND far (its centre
             * past skydist) is that backdrop and nothing the player is near or
             * the ship (whose top sits under skyhi). skycull = 0 keeps it. */
            if (g_skyCull) {
                float hyc = py[0], ccx = 0.0f, ccz = 0.0f;
                int j4;
                for (j4 = 0; j4 < 4; j4++) {
                    if (py[j4] > hyc) hyc = py[j4];
                    ccx += px[j4]; ccz += pz[j4];
                }
                ccx *= 0.25f; ccz *= 0.25f;
                if (hyc > (float)g_skyHi) {
                    float dd2 = ccx*ccx + ccz*ccz;
                    if (dd2 > (float)g_skyDist * (float)g_skyDist) {
                        g_skyCullN++;
                        return;
                    }
                }
            }
            g_passKept[slot]++;
            if (g_passDump && (g_passDump == 7 || g_passDump == dir + 1))
                passDumpAdd(dir, q[1], layer, g_exOn ? 'x' : 'h',
                            bpx, bpy, bpz, px, py, pz);
            radial = 1;
            {   /* centroid, OpenXR: x right, y up, -z forward */
                float cx3 = 0, cy3 = 0, cz3 = 0, ax, ay, az; int d6;
                for (j = 0; j < 4; j++) { cx3 += px[j]; cy3 += py[j]; cz3 += pz[j]; }
                ax = cx3 < 0 ? -cx3 : cx3; ay = cy3 < 0 ? -cy3 : cy3; az = cz3 < 0 ? -cz3 : cz3;
                if (az >= ax && az >= ay) d6 = cz3 < 0 ? 0 : 1;      /* front / back */
                else if (ax >= ay)        d6 = cx3 < 0 ? 2 : 3;      /* left / right */
                else                      d6 = cy3 > 0 ? 4 : 5;      /* up / down */
                g_passDirHist[slot][d6]++;
            }
            if (!g_passSampleOk[slot] && g_passKept[slot] == 20) {
                for (j = 0; j < 4; j++) {
                    g_passSample[slot][0][j] = rsx[j]; g_passSample[slot][1][j] = rsy[j];
                    g_passSample[slot][2][j] = rw[j];
                    g_passSample[slot][3][j] = px[j]; g_passSample[slot][4][j] = py[j];
                    g_passSample[slot][5][j] = pz[j];
                }
                g_passSampleOk[slot] = 1;
            }
        }
    }
    /* ------------------------------------------- quads nobody's pass drew
     * Three hundred-odd quads a frame never go through 0x00440D00 at all:
     * game logic calls the object drawer 0x004421F0 directly - there are
     * ninety-odd such call sites and exactly ONE of them is inside the chunk
     * list walk. Cars, props, the things that turn up and go away. They are
     * counted as "nonworld" in the log and, until now, they were the only
     * quads in the frame still sorted by the ENGINE's w while everything
     * around them had been re-keyed radially.
     *
     * Two key spaces in one sorted list is not a near miss, it is a
     * different curve: the engine's offset is z * 8, ours is
     * (LAYER-1) * d/(d+8000). At sixty metres the engine says 64000 and we
     * say 131000. A prop behind a wall therefore gets a SMALLER key than the
     * wall, is painted after it, and shows through it. That is the "object
     * through the wall" that has been in Known issues since the beginning.
     *
     * These quads come from the game's own forward camera, so their view
     * space is the native one and the radial depth is the same measurement
     * as everywhere else - they simply have to be keyed by it too. */
    if (g_nwRadial && g_passOn && g_camState == 1 &&
        !g_inWorld && !g_pass && !behind)
        radial = 1;

    if (radial) {
        /* the radial depth of each corner, and the sort key by the SAME rule
         * the engine applies to w (bits 10-11 of flags): a road strip is keyed
         * on its far edge, not on the corner under your feet, so it stays
         * behind the buildings standing on it. Always-min was painting the
         * asphalt over their lower floors. */
        DWORD kmin = 0xFFFFFFFFu, kmax = 0; unsigned __int64 ksum = 0;
        for (i = 0; i < 4; i++) {
            float d2 = px[i]*px[i] + py[i]*py[i] + pz[i]*pz[i];
            DWORD dk = radialKey((float)sqrt((double)d2));
            wrad[i] = layer * LAYER + dk;
            if (wrad[i] < kmin) kmin = wrad[i];
            if (wrad[i] > kmax) kmax = wrad[i];
            ksum += wrad[i];
        }
        switch ((q[0] >> 10) & 3) {
        case 0:  key = kmin; break;
        case 1:  key = kmax; break;
        case 2:  key = (DWORD)(ksum >> 2); break;
        default: key = g_prevKey - 1; break;
        }
        g_prevKey = key;
    }

    /* A polygon the projection deleted has no sort key: its four w are zero,
     * which would put it in front of the whole world. Rebuild one on the scale
     * the engine uses (w mod 0x40000 == depth * 8) but from the RADIAL
     * distance, not from z - z goes negative behind you and would sort
     * backwards, distance is right in every direction. Only these quads are
     * touched; the order of the forward scene is exactly as before. */
    if (behind) {
        float dmin = 1e30f;
        DWORD dk;
        for (i = 0; i < 4; i++) {
            float d2 = px[i]*px[i] + py[i]*py[i] + pz[i]*pz[i];
            if (d2 < dmin) dmin = d2;
        }
        dk = (DWORD)sqrt((double)dmin) * 8u;
        if (dk > LAYER - 1) dk = LAYER - 1;
        key = layer * LAYER + dk;
        g_behindQ++;
    }

    /* Light, read from 0x100051C2 (transform) and 0x10003FD0 / 0x100048E0
     * (use). Per channel: R from +0x4C, B from +0x50, G from +0x54, the raw
     * value becomes flags&4 ? s/2 : s*2-0x20, then the global light of slot
     * +0x38 and, when flags bit 18 is set, a per vertex offset from +0x5C..
     * +0x68 are added. For a textured quad 255 is added on top - the shade is
     * an attenuation below white. For a flat quad the 5-5-5 colour of the id
     * field times 8 takes the place of that 255. */
    {
        int c, i2, t[3];
        DWORD id = q[2];
        for (c = 0; c < 3; c++) {
            int v = (int)q[19 + c];
            t[c] = (q[0] & 4) ? v / 2 : v * 2 - 0x20;
        }
        if (flat) {
            base[0] = (int)((id      ) & 0x1F) * 8 + t[0] + g_amb[0];
            base[1] = (int)((id >>  5) & 0x1F) * 8 + t[2] + g_amb[2];
            base[2] = (int)((id >> 10) & 0x1F) * 8 + t[1] + g_amb[1];
        } else {
            base[0] = t[0] + g_amb[0] + 255;
            base[1] = t[2] + g_amb[2] + 255;
            base[2] = t[1] + g_amb[1] + 255;
        }
        for (i2 = 0; i2 < 4; i2++)
            vx[i2] = (q[0] & 0x40000) ? (int)q[23 + i2] : 0;
        if (g_exOn && (q[0] & 0x40000)) {       /* a piece: blend the parent's corner shades */
            int c0 = (int)q[23], c1 = (int)q[24], c2 = (int)q[25], c3 = (int)q[26];
            for (i2 = 0; i2 < 4; i2++) {
                float sf = g_exST[i2][0], tf = g_exST[i2][1];
                vx[i2] = (int)((1 - sf) * (1 - tf) * c0 + sf * (1 - tf) * c1 +
                               sf * tf * c2 + (1 - sf) * tf * c3);
            }
        }
        for (i2 = 0; i2 < 4; i2++) {
            int ch[3];
            for (c = 0; c < 3; c++) {
                int v = base[c] + vx[i2];
                if (!g_doShade) v = flat ? base[c] : 255;
                if (v < 0) v = 0;
                if (v > 255) v = 255;
                ch[c] = v;
            }
            if (g_doShade == 1 && !flat)
                ch[0] = ch[1] = ch[2] = (ch[0] + ch[1] + ch[2]) / 3;
            if (g_neutral) ch[0] = ch[1] = ch[2] = 255;
            for (c = 0; c < 3; c++) {
                int v = ch[c] * (int)g_texGain / 100;
                ch[c] = v > 255 ? 255 : v;
            }
            vcol[i2] = ((DWORD)(g_alphaMode == 1 ? 0x00 : g_alphaMode == 2 ? 0xC0 : 0x40) << 24) | ((DWORD)ch[2] << 16) |
                       ((DWORD)ch[1] << 8) | (DWORD)ch[0];
        }
        sh[0] = sh[1] = sh[2] = 255;
    }

    if (g_probeAt && g_probeN <= PROBE_MAX) {
        int pi;
        for (pi = 0; pi < g_probeN; pi++)
            if (g_probeId[pi] == q[1]) { g_probeCnt[pi]++; break; }
        if (pi == g_probeN && g_probeN < PROBE_MAX) {
            g_probeId[g_probeN] = q[1];
            g_probeCnt[g_probeN] = 1;
            g_probeN++;
        }
    }
    (void)g_texMap;
    if (g_qrBuildN < QRECT_MAX) {
        QRect *qr = &g_qrBuild[g_qrBuildN];
        float sx, sy;
        int i2;
        qr->id = q[1];
        qr->sh[0] = qr->sh[1] = qr->sh[2] = 0.0f;
        qr->x0 = qr->y0 = 1e9f; qr->x1 = qr->y1 = -1e9f;
        for (i2 = 0; i2 < 4; i2++) {
            sx = *(float *)&q[3 + i2 * 4];
            sy = *(float *)&q[4 + i2 * 4];
            if (sx < qr->x0) qr->x0 = sx;
            if (sx > qr->x1) qr->x1 = sx;
            if (sy < qr->y0) qr->y0 = sy;
            if (sy > qr->y1) qr->y1 = sy;
        }
        g_qrBuildN++;
        if (qr->x1 - qr->x0 > 500.0f && qr->y1 - qr->y0 > 380.0f) {   /* [probe] screen-filling quad */
            LONG w = (InterlockedIncrement(&g_bqW) - 1) & 7;
            g_bqS++; g_bqR[w].id = q[1]; g_bqR[w].w = q[6]; g_bqR[w].col = vcol[0];
            g_bqR[w].x0 = (int)qr->x0; g_bqR[w].y0 = (int)qr->y0; g_bqR[w].x1 = (int)qr->x1; g_bqR[w].y1 = (int)qr->y1;
        }
    }

    if (tr) {
        /* UV corners, HGL_D3D jump table 0x100056C0 on (flags>>4)&3: the
         * three real cases are straight, mirrored across u, mirrored across v
         * (cases 1 and 3 share code). Vertices leave as a strip 0,1,3,2. */
        static const int uvx[3][4] = { {0,1,1,0}, {1,0,0,1}, {0,1,1,0} };
        static const int uvy[3][4] = { {0,0,1,1}, {0,0,1,1}, {1,1,0,0} };
        int m = (int)((q[0] >> 4) & 3);
        LONG forced = g_uvOrder;
        if (m == 3) m = 1;
        if (forced >= 0) m = (int)(forced % 3);
        col = vcol[0];
        for (i = 0; i < 4; i++) {
            qu[i] = uvx[m][i] ? tr->u1 : tr->u0;
            qv[i] = uvy[m][i] ? tr->v1 : tr->v0;
        }
        if (g_exOn) {
            /* the same table, read at a fraction: corner k of the parent sits
             * at (s,t) = (0,0) (1,0) (1,1) (0,1), so u runs with s (mirrored
             * for m == 1) and v with t (mirrored for m == 2) */
            for (i = 0; i < 4; i++) {
                float sf = g_exST[i][0], tf = g_exST[i][1];
                if (m == 1) sf = 1.0f - sf;
                if (m == 2) tf = 1.0f - tf;
                qu[i] = tr->u0 + (tr->u1 - tr->u0) * sf;
                qv[i] = tr->v0 + (tr->v1 - tr->v0) * tf;
            }
        }
    } else {
        col = flat ? vcol[0] : ((tintOf(q[1], layer) & 0x00FFFFFFu) |
                                ((DWORD)(g_alphaMode == 1 ? 0x00 : g_alphaMode == 2 ? 0xC0 : 0x40) << 24));
        qu[0] = qu[1] = qu[2] = qu[3] = -1.0f;
        qv[0] = qv[1] = qv[2] = qv[3] = -1.0f;
    }
    (void)sh;

    if (tr) {
        DWORD cols[4];
        for (i = 0; i < 4; i++) cols[i] = vcol[i];
        wcRemember(px, py, pz, qu, qv, cols, q[1], layer);
    }
    if (g_buildCount / 6 < MAX_QUADS) {
        g_quadKey[g_buildCount / 6] = (unsigned __int64)key + 16;
        g_quadLayerB[g_buildCount / 6] = (unsigned char)(layer & 15);
    }
    {   float cq[3], dm, e1, e2, ar;
        LayerDist *L = &g_ld[layer & 15];
        cq[0] = (px[0]+px[1]+px[2]+px[3]) * 0.25f;
        cq[1] = (py[0]+py[1]+py[2]+py[3]) * 0.25f;
        cq[2] = (pz[0]+pz[1]+pz[2]+pz[3]) * 0.25f;
        dm = (float)sqrt((double)(cq[0]*cq[0] + cq[1]*cq[1] + cq[2]*cq[2])) / g_unitsPerMetre;
        if (!L->n || dm < L->dmin) L->dmin = dm;
        if (!L->n || dm > L->dmax) L->dmax = dm;
        L->n++;
        if (!g_pass) {          /* the backdrop rule counts only the engine pass,
                                 * so the rotated passes cannot inflate the tally */
            LayerDist *L0 = &g_ld0[layer & 15];
            if (!L0->n || dm < L0->dmin) L0->dmin = dm;
            if (!L0->n || dm > L0->dmax) L0->dmax = dm;
            L0->n++;
        }
        e1 = (float)sqrt((double)((px[1]-px[0])*(px[1]-px[0]) + (py[1]-py[0])*(py[1]-py[0]) +
                                  (pz[1]-pz[0])*(pz[1]-pz[0])));
        e2 = (float)sqrt((double)((px[3]-px[0])*(px[3]-px[0]) + (py[3]-py[0])*(py[3]-py[0]) +
                                  (pz[3]-pz[0])*(pz[3]-pz[0])));
        ar = e1 * e2 / (g_unitsPerMetre * g_unitsPerMetre);
        if (ar > g_bigArea) { g_bigArea = ar; g_bigDist = dm; g_bigTex = q[1]; }
        /* and the one that FILLS the view: area over distance squared. That
         * is the thing being stared at, whatever the log's biggest says. */
        if (dm > 0.05f) {
            float sr = ar / (dm * dm);
            if (sr > g_wideSr) { g_wideSr = sr; g_wideDist = dm; g_wideArea = ar; g_wideTex = q[1]; }
        }
    }
    /* ------------------------------------------------- far layers, pushed out
     * The engine's depth word saturates at 32767 units - 245 metres - so
     * nothing in this game can BE further away than that. A skyline half a
     * kilometre off therefore cannot be modelled where it stands; it is
     * modelled small and placed near, which in a sixty degree window is
     * indistinguishable from the real thing and in a headset is a toy across
     * the road that the eyes cannot converge on and that swims with every
     * movement of the head.
     *
     * Multiplying every corner by the same factor is a scale ABOUT THE EYE:
     * each corner stays on its own ray, so the picture does not move by a
     * pixel - only the distance does, and with it the parallax and the
     * convergence. The sort key is left alone, so the paint order is still
     * the engine's and the backdrop still goes down first.
     *
     * Which geometry, is the question the layer mask answers: the backdrop
     * has to be drawn behind everything, and behind everything in this
     * engine means its own sort layer (the top bits of w). farlayers = 0
     * leaves all of this inert. */
    if (g_farLayers & (1u << (layer & 15))) {
        float k = (float)g_farScale / 100.0f;
        if (k > 0.01f && (k < 0.99f || k > 1.01f))
            for (i = 0; i < 4; i++) { px[i] *= k; py[i] *= k; pz[i] *= k; }
    }
    /* ------------------------------------------------ backdrop by layer census
     * A faked skyline is a whole sort layer that is a HANDFUL of quads, all
     * sitting well out. Measured live on stage 1: L3 is 10 quads at 16-22 m -
     * the distant buildings drawn small and near, the toy across the road the
     * eyes cannot converge on. Stage 2's L3 is 1548 quads reaching in to 5 m -
     * the ship and the quay you stand on, real geometry. The layer number
     * cannot tell them apart; the COUNT and the NEAR EDGE can, and the DLL
     * already keeps both per layer from the previous frame (g_ldS). So decide
     * here, every frame, with no camera motion needed (which is what killed
     * autofar when the rail is parked): few quads, none of them close, scale
     * the layer out along its own rays - picture and laser unchanged, only the
     * distance and the convergence move. farlayerauto = 0 turns it off. */
    if (g_farAuto && !behind && (layer & 15) < 16) {
        LayerDist *L = &g_ld0S[layer & 15];
        if (L->n > 0 && L->n <= (DWORD)g_farAutoCount &&
            L->dmin >= (float)g_farAutoNear) {
            float k = (float)g_farScale / 100.0f;
            if (k > 1.01f)
                for (i = 0; i < 4; i++) { px[i] *= k; py[i] *= k; pz[i] *= k; }
        }
    }
    /* autofar: measure on the raw corners, then push what has been found to
     * ride with the camera. The engine's own pass only - a rotated pass sees
     * the same points through another matrix and would muddy the shift. */
    if (g_autoFar && !g_pass && q[1] < AF_TEX) {
        AfAcc *a = &g_afAcc[q[1]];
        a->sx += (px[0]+px[1]+px[2]+px[3]) * 0.25f;
        a->sy += (py[0]+py[1]+py[2]+py[3]) * 0.25f;
        a->sz += (pz[0]+pz[1]+pz[2]+pz[3]) * 0.25f;
        a->n++;
        if (g_afState[q[1]] == 1 && g_afDist[q[1]] >= (float)g_afMin) {
            float k = (float)g_farScale / 100.0f;
            if (k > 1.01f) {
                for (i = 0; i < 4; i++) { px[i] *= k; py[i] *= k; pz[i] *= k; }
                g_afApplied++;
            }
        }
    }
    if (g_aimArm && !g_pass && g_share && g_aimN < AIM_MAX) {
        float ax = g_share->aim_x, ay = g_share->aim_y;
        float bx0 = 1e9f, bx1 = -1e9f, by0 = 1e9f, by1 = -1e9f;
        int j;
        for (j = 0; j < 4; j++) {
            float sxj = *(float *)&q[3 + j * 4], syj = *(float *)&q[4 + j * 4];
            if (sxj < bx0) bx0 = sxj;
            if (sxj > bx1) bx1 = sxj;
            if (syj < by0) by0 = syj;
            if (syj > by1) by1 = syj;
        }
        if (ax >= bx0 - 1.0f && ax <= bx1 + 1.0f &&
            ay >= by0 - 1.0f && ay <= by1 + 1.0f) {
            AimRec *a = &g_aim[g_aimN++];
            float ax3 = (px[0] + px[1] + px[2] + px[3]) * 0.25f;
            float ay3 = (py[0] + py[1] + py[2] + py[3]) * 0.25f;
            float az3 = (pz[0] + pz[1] + pz[2] + pz[3]) * 0.25f;
            a->tex = q[1]; a->flags = q[0]; a->ra = g_quadRa;
            a->layer = (int)(layer & 15);
            a->trueN = trueN;
            a->path = g_pass ? 2 : (g_inWorld ? 0 : 1);
            a->dm = (float)sqrt((double)(ax3*ax3 + ay3*ay3 + az3*az3)) / g_unitsPerMetre;
            a->x0 = (int)bx0; a->x1 = (int)bx1;
            a->y0 = (int)by0; a->y1 = (int)by1;
            for (j = 0; j < 4; j++) {
                DWORD wf = q[6 + j * 4];
                a->w[j] = wf;
                a->zm[j] = (float)(wf % LAYER) / 8.0f / g_unitsPerMetre;
            }
        }
    }
    for (i = 0; i < 6; i++) {
        int k = order[i];
        DWORD wfull = behind ? key : radial ? wrad[k] : q[6 + k * 4];
        float dn = 1.0f - (float)wfull / 4194304.0f;   /* 16 layers span */
        if (dn < 0.0f) dn = 0.0f;
        if (dn > 1.0f) dn = 1.0f;
        g_build[g_buildCount].x = px[k];
        g_build[g_buildCount].y = py[k];
        g_build[g_buildCount].z = pz[k];
        g_build[g_buildCount].col = (flat || tr) ? vcol[k] : col;
        if (g_distDebug) {
            /* Painted FLAT, with no texture at all.
             *
             * The first cut kept the texture coordinates and only tinted the
             * vertex colour - and the shader computes texel * colour, so a
             * "green" band written 0x40D040 scales the whole surface to a
             * quarter of its brightness and a "blue" one to a fifth. That is
             * why the depth view only ever went dark: it was never showing a
             * band, it was dimming the game by a different amount per band.
             * A debug view has to be readable, so u = v = -1 - the shader's
             * "no texture, take the colour as it is" - and the band is then
             * the only thing on the screen.
             *
             *   1  by distance: red under 10 m, orange 25, yellow 50,
             *      green 100, cyan 200, blue beyond
             *   2  by the engine's own sort layer (w / 0x40000), sixteen
             *      colours - a backdrop drawn in its own layer stands out
             *      whatever distance it claims
             *   3  by submission path: green = the game's own world pass,
             *      blue = one of our rotated passes, red = outside both
             *      (the "nonworld" quads, 300-odd a frame from 0x0044293B)
             *
             * Vertex colour is 0xAABBGGRR, so every literal here reads BGR. */
            static const DWORD layCol[16] = {
                0x4040FFu, 0x40FF40u, 0xFF4040u, 0x40FFFFu,
                0xFF40FFu, 0xFFFF40u, 0x4090FFu, 0x90FF40u,
                0xFF9040u, 0x9040FFu, 0x40FF90u, 0xFF4090u,
                0xC0C0C0u, 0x303030u, 0x00A5FFu, 0xFFFFFFu };
            DWORD rgb;
            if (g_distDebug == 2) {
                rgb = layCol[layer & 15];
            } else if (g_distDebug == 4) {
                /* which pass drew it. distdebug 3 says only "one of ours";
                 * this says WHICH, and the passes tessellate the road each
                 * around its own camera, so a shard on the ground belongs to
                 * exactly one of them. 0xBBGGRR. */
                static const DWORD passCol[8] = {
                    0x40FF40u,   /* 0 front - the engine's own pass: green   */
                    0x4040FFu,   /* 1 back:  red                             */
                    0xFF4040u,   /* 2 left:  blue                            */
                    0x40FFFFu,   /* 3 right: yellow                          */
                    0xFF40FFu,   /* 4 up:    magenta                         */
                    0xFFFF40u,   /* 5 down:  cyan                            */
                    0xFFFFFFu,   /* 6 xfront: white                          */
                    0x808080u };
                rgb = passCol[(int)g_pass & 7];
            } else if (g_distDebug == 3) {
                rgb = g_pass ? 0xFF4040u : g_inWorld ? 0x40FF40u : 0x4040FFu;
            } else {
                float dx = px[k], dy = py[k], dz = pz[k];
                float dd = (float)sqrt((double)(dx*dx + dy*dy + dz*dz)) / g_unitsPerMetre;
                rgb = dd <  10.0f ? 0x2030FFu :      /* red    */
                      dd <  25.0f ? 0x2090FFu :      /* orange */
                      dd <  50.0f ? 0x20E0FFu :      /* yellow */
                      dd < 100.0f ? 0x40D040u :      /* green  */
                      dd < 200.0f ? 0xD0C030u :      /* cyan   */
                                    0xFF4030u;       /* blue   */
            }
            g_build[g_buildCount].col = 0x40000000u | rgb;
            qu[k] = -1.0f;                  /* flat: the shader ignores the atlas */
            qv[k] = -1.0f;
        }
        g_build[g_buildCount].u = qu[k];
        g_build[g_buildCount].v = qv[k];
        g_build[g_buildCount].d = g_zflip ? 1.0f - dn : dn;
        g_buildCount++;
    }
}

/* ------------------------------------------------- exact polygon identity
 * Keyed on texture, layer and the twelve true view-space coordinates of the
 * polygon, compared exactly. The rotated passes see the same polygon through
 * a view matrix that is the native one post-multiplied by a 0/+-1 matrix, so
 * the coordinates that reach the projector are sign-and-order permutations
 * of the native ones and unrotate to the same bits (-0 compares equal to 0
 * as floats, which is why the compare is on floats, not on the words). */
static void exactClear(void)
{
    int i;
    g_exsN = 0;
    for (i = 0; i < EXS_HEAD; i++) g_exsHead[i] = -1;
}
static void exactFrameClear(void) { if (g_exs) exactClear(); }

/* 1 = a pass already drew this polygon (registers it otherwise) */
static int exactSeen(DWORD tex, DWORD layer, const float *px, const float *py, const float *pz)
{
    float k[12];
    DWORD h;
    int i, e;
    if (!g_exs) {
        g_exs = (ExsEnt *)VirtualAlloc(NULL, sizeof(ExsEnt) * EXS_N, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
        if (!g_exs) return 0;
        exactClear();
    }
    for (i = 0; i < 4; i++) { k[i * 3] = px[i]; k[i * 3 + 1] = py[i]; k[i * 3 + 2] = pz[i]; }
    h = tex * 0x9E3779B1u;
    for (i = 0; i < 12; i++) {
        float f = k[i] == 0.0f ? 0.0f : k[i];             /* -0 and 0 hash alike */
        h ^= *(const DWORD *)&f + 0x85EBCA6Bu + (h << 6) + (h >> 2);
    }
    h &= EXS_HEAD - 1;
    for (e = g_exsHead[h]; e >= 0; e = g_exs[e].next) {
        const ExsEnt *p = &g_exs[e];
        /* The layer is NOT part of the identity: it comes out of the
         * engine's w for the pass that drew the quad, and the same polygon
         * gets a different layer under every rotated camera (seen live:
         * one far-chunk quad as L5 in the back pass, L3 right, L2 up).
         * Matching on it let every pass keep its own copy of the whole far
         * chunk - 30000 quads a frame at the quay. Texture and the twelve
         * coordinates say "same polygon"; the first pass keeps its layer. */
        if (p->tex != tex) continue;
        for (i = 0; i < 12; i++) if (p->k[i] != k[i]) break;
        if (i == 12) return 1;
    }
    if (g_exsN >= EXS_N) { g_exFull++; return 0; }
    e = g_exsN++;
    g_exSeenN++;
    for (i = 0; i < 12; i++) g_exs[e].k[i] = k[i];
    g_exs[e].tex = tex; g_exs[e].layer = layer;
    g_exs[e].next = g_exsHead[h];
    g_exsHead[h] = e;
    return 0;
}

/* ------------------------------------------------- the clipper, detoured
 *
 * 0x00443CC0 (object types 1..3 - the road among them) transforms every
 * vertex, projects it, and for each polygon: all four w > 0 -> submit the
 * quad as it is; none -> skip; some -> 0x00442960(view xyz[4], poly, uv,
 * depth = 2, layer). That clipper projects the four corners, four edge
 * midpoints and the centre, and takes the four quarters in turn: a quarter
 * with all four w > 0 is submitted, one with none is dropped, one with some
 * recurses with depth * 2 until depth > 0x20 - and THEN the quarter that
 * still straddles the near plane is dropped. What reaches us from a
 * straddling polygon is therefore a set of quarters-of-quarters, each with
 * its own projected corners, and a wedge missing where the near plane runs.
 * Projected corners are what every artefact was made of: a corner a few
 * units in front of the near plane divides by a tiny z and is pinned to
 * +-10000 (clampdrop), one behind it is written as (cx, cy, 0, 0) (neardrop),
 * one past 32767 units keeps its screen position but not its depth
 * (passtol). Reconstructing from those is guessing.
 *
 * The clipper's first argument is the polygon itself, in view space, before
 * any of that. So: at the top-level call (depth == 2) remember it, let the
 * engine run (its pieces feed the flat game window and are held back from VR
 * in wrap_quad; the first of them lends its record - flags, texture, shade),
 * and then emit the polygon for VR from the true corners: quartered exactly
 * as the engine quarters it, so the painter's keys are the engine's, but
 * with nothing dropped - the straddling quarter at the depth limit and the
 * quarters behind the eye go out whole. The headset renderer projects and
 * clips them properly. A polygon the engine never handed to the clipper -
 * all four corners in front - arrives as a whole quad and gets its corners
 * from the projector hook instead; both kinds are exact and both are
 * deduplicated across the passes by identity, see exactSeen. */
#define CLIP_FUNC 0x00442960
static const BYTE CLIP_SIG[] = { 0x8B,0x44,0x24,0x10, 0x81,0xEC,0xE0,0x01,0x00,0x00 };
static void (__cdecl *g_clipOrig)(const float *v, void *poly, void *uv, int depth, DWORD layer);
static volatile LONG g_clipState;      /* 0 off, 1 hooked, 2 not found, 3 denied */

static void exactPiece(DWORD *rec, const float xyz[4][3], const float st[4][2], DWORD layer, float nearz)
{
    int i;
    /* a record for the piece: sx/sy/rhw/w written the way the projector
     * would (only the probes and the non-pass sort key read them) */
    for (i = 0; i < 4; i++) {
        float x = xyz[i][0], y = xyz[i][1], z = xyz[i][2];
        DWORD *c = &rec[3 + i * 4];
        if (z < nearz) {                /* layer is the engine's raw argument, e.g. 0x1C0000 */
            *(float *)&c[0] = g_cx; *(float *)&c[1] = g_cy;
            c[2] = 0; c[3] = layer;
        } else {
            float ox = x * g_fx / z, oy = y * g_fy / z;
            DWORD dk = z > 32767.0f ? 0x3FFF8u : (DWORD)(z * 8.0f + 0.5f);
            if (ox < -10000.0f) ox = -10000.0f; if (ox > 10000.0f) ox = 10000.0f;
            if (oy < -10000.0f) oy = -10000.0f; if (oy > 10000.0f) oy = 10000.0f;
            *(float *)&c[0] = g_cx + ox; *(float *)&c[1] = g_cy + oy;
            *(float *)&c[2] = 1.0f / z; c[3] = layer + dk;
        }
        g_exXyz[i][0] = x; g_exXyz[i][1] = y; g_exXyz[i][2] = z;
        g_exST[i][0] = st[i][0]; g_exST[i][1] = st[i][1];
    }
    g_exOn = 1;
    pushQuad(rec);
    g_exOn = 0;
    g_clipPieces++;
}

/* the engine's own recursion, minus the drops */
static void exactSplit(DWORD *rec, const float v[4][3], const float st[4][2], int depth, DWORD layer, float nearz)
{
    int i, in = 0;
    for (i = 0; i < 4; i++) if (v[i][2] >= nearz) in++;
    if (in == 0 || in == 4 || depth > g_splitDepth || g_buildCount + 6 * 4 > MAX_QUADS * 6) {
        if (in != 0 && in != 4) {
            g_clipDeep++;
            /* This piece still has the eye plane running through it, and no
             * amount of further quartering will change that - the engine
             * throws such a piece away, we keep it whole and let the headset
             * clip it. A piece that CONTAINS the eye has no honest projection:
             * its far corners go to infinity and its depth key is whatever the
             * corner behind the eye was written as. If the giant road-textured
             * plane is one of these, this key kills it. */
            if (g_deepDrop) { g_deepDropped++; return; }
        }
        if (in == 0 && g_behindDrop) { g_behindDropped++; return; }
        exactPiece(rec, v, st, layer, nearz);
        return;
    }
    {
        float m[4][3], c[3], ms[4][2], cs[2], q[4][3], qs[4][2];
        int k, a;
        for (i = 0; i < 4; i++) {
            int j = (i + 1) & 3;
            for (k = 0; k < 3; k++) m[i][k] = (v[i][k] + v[j][k]) * 0.5f;
            for (k = 0; k < 2; k++) ms[i][k] = (st[i][k] + st[j][k]) * 0.5f;
        }
        for (k = 0; k < 3; k++) c[k] = (m[0][k] + m[2][k]) * 0.5f;
        for (k = 0; k < 2; k++) cs[k] = (ms[0][k] + ms[2][k]) * 0.5f;
        /* quarter a: corner a, then round the outline through the centre */
        for (a = 0; a < 4; a++) {
            int prev = (a + 3) & 3;
            const float *p0 = v[a], *p1 = m[a], *p2 = c, *p3 = m[prev];
            const float *s0 = st[a], *s1 = ms[a], *s2 = cs, *s3 = ms[prev];
            for (k = 0; k < 3; k++) { q[0][k] = p0[k]; q[1][k] = p1[k]; q[2][k] = p2[k]; q[3][k] = p3[k]; }
            for (k = 0; k < 2; k++) { qs[0][k] = s0[k]; qs[1][k] = s1[k]; qs[2][k] = s2[k]; qs[3][k] = s3[k]; }
            exactSplit(rec, q, qs, depth * 2, layer, nearz);
        }
    }
}

static void exactPolygon(const float v[4][3], DWORD layer)
{
    static const float st0[4][2] = { {0,0}, {1,0}, {1,1}, {0,1} };
    DWORD rec[27];
    float px[4], py[4], pz[4], nearz = 0.0f;
    BYTE *base = (BYTE *)GetModuleHandleA(NULL);
    int i, dir;
    if (base && !IsBadReadPtr(base + 0xCF800, 4)) nearz = *(float *)(base + 0xCF800);
    CopyMemory(rec, g_clipRec, sizeof(rec));
    /* whole-polygon identity, in true view space, decided once */
    if (g_passOn && g_camState == 1 && (g_inWorld || g_pass)) {
        dir = (g_pass >= 1 && g_pass <= 5) ? (int)g_pass : 0;
        for (i = 0; i < 4; i++) { px[i] = v[i][0]; py[i] = -v[i][1]; pz[i] = -v[i][2]; }
        passUnrotate(dir, px, py, pz);
        if (exactSeen(rec[1], layer / LAYER, px, py, pz) && g_pass) { g_clipDup++; return; }
    }
    exactSplit(rec, v, st0, 2, layer, nearz);
}

static void __attribute__((force_align_arg_pointer)) __cdecl
clipThunk(const float *v, void *poly, void *uv, int depth, DWORD layer)
{
    float c[4][3];
    if (!g_trueClip || depth != 2 || g_inClip || !v || IsBadReadPtr(v, 48)) {
        g_clipOrig(v, poly, uv, depth, layer);
        return;
    }
    CopyMemory(c, v, 48);
    g_clipRecOk = 0; g_clipEmit = 0;
    g_inClip = 1;
    g_clipOrig(v, poly, uv, depth, layer);
    g_inClip = 0;
    g_clipPoly++;
    if (!g_clipRecOk) { g_clipNoRec++; return; }   /* backfacing: the engine drew none of it */
    if (!(g_ready || g_doShare)) return;
    EnterCriticalSection(&g_lock);
    exactPolygon((const float (*)[3])c, layer);
    LeaveCriticalSection(&g_lock);
}

/* 0x00442960: mov eax,[esp+0x10] / sub esp,0x1E0 - ten bytes, the second
 * instruction straddles the five-byte jump, so both go to the trampoline. */
static void installClipHook(BYTE *base)
{
    BYTE *p = base + (CLIP_FUNC - 0x00400000), *tr;
    DWORD old;
    int i;
    if (!g_trueClip || g_clipState || !base) return;
    if (IsBadReadPtr(p, sizeof(CLIP_SIG))) { g_clipState = 2; return; }
    if (p[0] == 0xE9) { g_clipState = g_clipOrig ? 1 : 3; return; }
    for (i = 0; i < (int)sizeof(CLIP_SIG); i++)
        if (p[i] != CLIP_SIG[i]) { g_clipState = 2; return; }
    tr = (BYTE *)VirtualAlloc(NULL, 32, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
    if (!tr) { g_clipState = 3; return; }
    for (i = 0; i < (int)sizeof(CLIP_SIG); i++) tr[i] = p[i];
    tr[10] = 0xE9;
    *(LONG *)(tr + 11) = (LONG)(LONG_PTR)((p + 10) - (tr + 15));
    g_clipOrig = (void (__cdecl *)(const float *, void *, void *, int, DWORD))tr;
    if (!VirtualProtect(p, 10, PAGE_EXECUTE_READWRITE, &old)) { g_clipState = 3; g_clipOrig = NULL; return; }
    p[0] = 0xE9;
    *(LONG *)(p + 1) = (LONG)(LONG_PTR)((BYTE *)clipThunk - (p + 5));
    for (i = 5; i < 10; i++) p[i] = 0x90;
    VirtualProtect(p, 10, old, &old);
    FlushInstructionCache(GetCurrentProcess(), p, 10);
    {
        HMODULE keep = NULL;
        GetModuleHandleExA(0x00000001 | 0x00000004, (LPCSTR)(void *)clipThunk, &keep);
    }
    g_clipState = 1;
}

/* Sprites, HGL_D3D 0x100056E0. A sprite is a screen rectangle: corners at
 * +0x0C/+0x10 and +0x1C/+0x20, texture at +0x04, shade at +0x4C.., and the w
 * of the first vertex (+0x18) clamped to 3 as a priority. This is how the sky
 * and the HUD reach the screen - as flat 2D blits with no depth of their own,
 * so here the big ones go far away behind the world and the small ones stay
 * close as an overlay. */
static void pushSprite(const DWORD *s)
{
    float x0 = *(const float *)&s[3], y0 = *(const float *)&s[4];
    float x1 = *(const float *)&s[7], y1 = *(const float *)&s[8];
    const TexReg *tr;
    float sx[4], sy[4], dist;
    int back;
    DWORD col;
    int i, order[6] = { 0, 1, 2, 0, 2, 3 };
    int prio = (int)s[6];

    if (prio < 0) prio = 0;
    if (prio > 3) prio = 3;
    /* ------------------------------------------------ reading the game's HUD
     * The overlay is a fixed cast of texture ids, so the state it displays can
     * simply be read off it - no counters to find in memory, no scanning.
     *
     * The ammo drum is not one picture but twenty-one per player: 1378..1398
     * for player 1, 1399..1419 for player 2, in three banks of seven - steady,
     * mid-recoil, muzzle flash - each running from a full cylinder down to an
     * empty one. Proven from a live dump: every shot walks the drum through
     * (1392, 1386, 1379), then (1393, 1387, 1380), and so on to
     * (1397, 1391, 1384), after which a reload returns it to 1378. So the
     * seven steps of a bank ARE the round count, and
     *     rounds = 6 - ((id - base) % 7)
     * holds in all three banks (during the flash frame it names the round
     * that is still in the cylinder, which is what the art shows anyway).
     *
     * Lives are simpler still: 1377 is drawn once per life. Player 1's row
     * runs right from x = 72, player 2's runs left from x = 538, so the side
     * of the screen tells them apart. Counted, not decoded. */
    if (s[1] >= 1378 && s[1] <= 1419) {
        int p2 = (s[1] >= 1399);
        g_ammoId[p2] = s[1];
        if (g_hudOwn) return;
    } else if (s[1] == 1377) {
        int p2 = (x0 >= (float)g_cx);
        if (g_lifeN[p2] < 32) g_lifeN[p2]++;
        if (g_hudOwn) return;
    }
    /* priority 0 is the game's crosshair; remember where it sits this frame so
     * the joystick hook can steer it onto the VR aim point (feedback loop). */
    if (prio == 0 && x1 > x0 && y1 > y0) {
        LONG w = (InterlockedIncrement(&g_candW) - 1) & (XHAIR_CAND - 1);
        g_candX[w] = (x0 + x1) * 0.5f;
        g_candY[w] = (y0 + y1) * 0.5f;
        g_candTex[w] = s[1];
        g_candT[w] = GetTickCount();
        g_xhairHits++;
    }
    /* THE GAME'S OWN CROSSHAIRS. Two live logs pinned the texture ids exactly:
     * player 1 cycles 1361..1368 and player 2 1369..1376, two sprites per
     * frame, and the clusters never mix (P1 sat at x=23 while P2 sat at x=616).
     * They exist because the flat game needs somewhere to show where a mouse
     * is pointing; here the laser does that, in 3D, and the flat sprite is a
     * second crosshair lagging behind the first by the servo loop. Drop it.
     * The candidate ring above is fed BEFORE this, so the feedback loop still
     * sees them - it just does not draw them. */
    /* Player 2 plays off this same picture on a monitor and has no laser, so
     * HIS crosshair is the only thing he can aim by - it must stay. Player 1
     * has the laser and does not need his. In akimbo there is no second
     * player: player 2 IS the headset's other hand, with its own laser and
     * its own gun model, so its flat crosshair is the same lagging duplicate
     * player 1's was, and mode 1 drops it too. 0 = keep both, 1 = drop player
     * 1's, and player 2's as well while akimbo is driving it (default),
     * 2 = always drop both, 3 = never drop player 2's, akimbo or not. */
    nearAim(s[1], 0, 1, prio, x0, y0, x1, y1, 0);
    if (g_hideXhair && s[1] >= 1361 && s[1] <= 1368) return;
    if (s[1] >= 1369 && s[1] <= 1376 &&
        (g_hideXhair == 2 || (g_hideXhair == 1 && g_akimboOn))) return;
    /* hudhide: drop overlay sprites by texture id outright. The car chase
     * dashboard is a flat cutout with nothing behind it - in a headset it
     * hangs in mid air over the road - and a player who would rather not see
     * it should not need a rebuild to say so. */
    if (g_hudHideN && idIn(g_hudHide, g_hudHideN, s[1])) return;

    if (g_sprN2 < 32) {                       /* telemetry for the [P] dump */
        g_sprInfo[g_sprN2].tex  = s[1];
        g_sprInfo[g_sprN2].prio = prio;
        g_sprInfo[g_sprN2].x0 = x0; g_sprInfo[g_sprN2].y0 = y0;
        g_sprInfo[g_sprN2].x1 = x1; g_sprInfo[g_sprN2].y1 = y1;
        g_sprN2++;
    }
    if (!g_doSprites) return;
    if (g_buildCount + 6 > MAX_QUADS * 6) return;
    if (!(x1 > x0) || !(y1 > y0)) return;
    tr = regFind(s[1]);
    if (!tr) return;
    if (tr->base != 0 && x1 - x0 < 300.0f && g_buildCount > 1200) {   /* [probe] small stage-bank sprite in play */
        LONG w = (InterlockedIncrement(&g_ssW) - 1) % 12;
        g_ssS++; g_ssR[w].tex = s[1]; g_ssR[w].prio = prio;
        g_ssR[w].x0 = (int)x0; g_ssR[w].y0 = (int)y0; g_ssR[w].x1 = (int)x1; g_ssR[w].y1 = (int)y1;
    }
    /* VC2VR_SHOT.LOG, 26 shots: the flash the game draws at the point of
     * impact is texture 1344 - startup bank, priority 3, 60x66, one frame,
     * centred on the aim point. Priority 3 sent it down the sky path (a white
     * blob smeared over the backdrop and repeated by the dome), and the
     * startup bank pinned it to the unzoomed focal length at sprdist. It is
     * neither sky nor HUD: it is an event in the world, at the live
     * projection, on the surface the ray hits. */
    if (s[1] == g_shotTex) {
        if (!g_shotSpr) return;
        prio = 2;
    }
    back = (prio == 3);
    /* Priority 3 is "drawn before everything else", not "is the sky". On the
     * driving stage the dashboard panel arrives at priority 3 too - the probe
     * caught it as texture 1546 at y 373..537, entirely BELOW the centre of
     * the screen. Wrapping that onto the sky cylinder is how the backdrop
     * started going mad. The panorama always straddles or sits above the
     * horizon; anything whose top edge is already below it is overlay. */
    if (back && y0 >= g_cy) { back = 0; prio = 2; }
    dist = back ? g_sprFar : g_sprDist;
    if (back && g_skyDome && tr->base != 0) {   /* [probe] stage-bank sprite on the sky path */
        LONG w = (InterlockedIncrement(&g_skW) - 1) & 7;
        g_skS++; g_skR[w].tex = s[1]; g_skR[w].x0 = x0; g_skR[w].y0 = y0; g_skR[w].x1 = x1; g_skR[w].y1 = y1;
        g_skR[w].sh = (int)s[19];
    }
    if (back && g_skyDome) {                 /* held back, wrapped at flush */
        if (g_skyN < 8) {
            g_sky[g_skyN].tex = s[1];
            g_sky[g_skyN].x0 = x0; g_sky[g_skyN].y0 = y0;
            g_sky[g_skyN].x1 = x1; g_sky[g_skyN].y1 = y1;
            g_sky[g_skyN].sh[0] = (float)(int)s[19];
            g_sky[g_skyN].sh[1] = (float)(int)s[20];
            g_sky[g_skyN].sh[2] = (float)(int)s[21];
            g_skyN++;
        }
        return;
    }

    sx[0] = x0; sy[0] = y0;
    sx[1] = x1; sy[1] = y0;
    sx[2] = x1; sy[2] = y1;
    sx[3] = x0; sy[3] = y1;

    {
        int c, ch[3];
        int t[3];
        /* 0x10003E12: the ambient is folded in only for priority 2 and 3 */
        int amb = prio > 1;
        t[0] = (int)s[19] + (amb ? g_amb[0] : 0) + 255;
        t[1] = (int)s[21] + (amb ? g_amb[2] : 0) + 255;
        t[2] = (int)s[20] + (amb ? g_amb[1] : 0) + 255;
        for (c = 0; c < 3; c++) {
            int v = g_doShade ? t[c] : 255;
            v = v * (int)g_texGain / 100;
            if (v < 0) v = 0;
            if (v > 255) v = 255;
            ch[c] = v;
        }
        col = ((DWORD)(g_alphaMode == 1 ? 0x00 : g_alphaMode == 2 ? 0xC0 : 0x40) << 24) | ((DWORD)ch[2] << 16) | ((DWORD)ch[1] << 8) |
              (DWORD)ch[0];
    }

    /* The [P] dump settled it: priority 3 is two 762x838 tiles that scroll
     * with the camera and sit on the horizon (y ends at 244 of 480) - that is
     * the sky. Priorities 0..2 are the tutorial box, the revolver, the five
     * hearts, the SEGA line: the overlay. So 3 goes far away and first, the
     * rest hang close and last, in order 2, 1, 0. */
    if (g_buildCount / 6 < MAX_QUADS)
        g_quadKey[g_buildCount / 6] = back ? 0xFFFFFFFFFull
                                           : (unsigned __int64)prio;
    /* The HUD is drawn by the game in pixels, so unprojecting it with the
     * live focal length makes it grow and shrink with the camera zoom - the
     * ammo drum swelling to fill the visor is not a bug in the game, it is us
     * treating a 2D overlay as if it were in the world. Priorities 0..2 are
     * overlay: hang them at the unzoomed focal length so they keep one size.
     * Priority 3 is the sky panorama, which IS an angle and must follow. */
    {
        /* Priority 0 is the crosshair: one sprite per frame, and it marks
         * where the gun points, so its pixel position only means anything
         * through the projection the game is using RIGHT NOW. Pinning it to
         * the unzoomed focal length put it at the wrong angle - that is the
         * offset between the two windows. Priorities 1 and 2 are the ammo
         * drum, lives and credits: those are flat overlay and must keep one
         * size whatever the zoom does. Priority 3 is the sky, an angle again. */
        /* Hit splashes drift the further from the middle of the screen they
         * are, and are exact dead centre. That shape - zero error at the
         * centre, growing towards the edges - is the signature of the wrong
         * focal length, because the angle is atan((sx - cx) / f) and only the
         * centre term survives when f is wrong. The splash was being pinned
         * to the unzoomed 554 while the game was projecting through 1400.
         * It is not HUD. It is an event in the world and must be placed
         * through the projection the game is using now.
         * The two are told apart by which bank the texture came from: the
         * overlay - crosshair, drum, hearts, CREDITS - is the bank uploaded
         * once at startup with base 0 (ids 0..1547 in every dump). Effects
         * belong to a stage bank, base 1600 or 1900. */
        int shot = (s[1] == g_shotTex);
        /* The dashboard's ids are 1603/1604, above the 1547 the startup
         * overlay bank ends at, so by the base test below it counts as an
         * EVENT IN THE WORLD: projected through the live focal length and,
         * with splashdepth on, ray cast against the scene and pinned to
         * whatever it lands on - which is the road. That is why a car's
         * dashboard is lying across the street. A named panel is none of
         * those things; it is the car you are sitting in, and it is placed
         * by hand below. */
        int panel = g_panelIdsN && !back && prio != 0 &&
                    idIn(g_panelIds, g_panelIdsN, s[1]);
        int world = panel ? 0 :
                    ((prio == 0) || back || shot ||
                     (g_hudFix == 0) ||
                     (g_hudFix == 1 && tr && tr->base != 0));
        float ffx = world ? g_fx : g_fxIni;
        float ffy = world ? g_fy : g_fyIni;
        if (g_buildCount / 6 < MAX_QUADS)
            g_quadFlat[g_buildCount / 6] = (unsigned char)((panel || !world) ? 1 : 0);
        /* A hit splash is an event ON a surface, not a card 2.3 m out: hung at
         * sprdist it sits halfway between the gun and the wall and drifts with
         * every head move. Cast the ray through the sprite's centre against the
         * world already in this frame's buffer and put it where it lands. */
        if (g_splashDepth && world && !back && prio != 0 && tr && (tr->base != 0 || shot)) {
            float mx = (sx[0] + sx[2]) * 0.5f, my = (sy[0] + sy[2]) * 0.5f;
            float dx = (mx - g_cx) / ffx, dy = -(my - g_cy) / ffy, dz = -1.0f;
            float best = 1e30f;
            UINT i2;
            for (i2 = 0; i2 + 2 < g_buildCount; i2 += 3) {
                const Vtx *a = &g_build[i2], *b = &g_build[i2 + 1], *c = &g_build[i2 + 2];
                float e1x, e1y, e1z, e2x, e2y, e2z, px2, py2, pz2, det, inv, u, v, t, qx, qy, qz;
                if (a->d >= 1.0f || a->d <= 0.0f) continue;      /* overlay or sky */
                e1x = b->x - a->x; e1y = b->y - a->y; e1z = b->z - a->z;
                e2x = c->x - a->x; e2y = c->y - a->y; e2z = c->z - a->z;
                px2 = dy * e2z - dz * e2y; py2 = dz * e2x - dx * e2z; pz2 = dx * e2y - dy * e2x;
                det = e1x * px2 + e1y * py2 + e1z * pz2;
                if (det > -1e-7f && det < 1e-7f) continue;
                inv = 1.0f / det;
                u = (-a->x * px2 - a->y * py2 - a->z * pz2) * inv;
                if (u < 0.0f || u > 1.0f) continue;
                qx = -a->y * e1z + a->z * e1y; qy = -a->z * e1x + a->x * e1z; qz = -a->x * e1y + a->y * e1x;
                v = (dx * qx + dy * qy + dz * qz) * inv;
                if (v < 0.0f || u + v > 1.0f) continue;
                t = (e2x * qx + e2y * qy + e2z * qz) * inv;
                if (t > 16.0f && t < best) best = t;
            }
            {
                UINT ntri = 0;
                for (i2 = 0; i2 + 2 < g_buildCount; i2 += 3)
                    if (g_build[i2].d < 1.0f && g_build[i2].d > 0.0f) ntri++;
                g_spTry++;
                if (best < 1e29f) g_spHit++; else if (!ntri) g_spNoWorld++; else g_spMiss++;
                if (ntri >= 200) {
                    LONG w = (InterlockedIncrement(&g_spSW) - 1) & 7;
                    g_spS[w].tex = s[1]; g_spS[w].prio = prio; g_spS[w].base = tr->base;
                    g_spS[w].nb = g_buildCount; g_spS[w].ntri = ntri;
                    g_spS[w].t = best < 1e29f ? best : -1.0f; g_spS[w].mx = mx; g_spS[w].my = my;
                }
            }
            if (best < 1e29f) {
                dist = best * 0.97f;
            } else if (g_sprMissFar > 0) {
                /* THE RAY FOUND NOTHING, AND sprdist IS 2.3 METRES.
                 * That default was chosen for a hit splash, which is small and
                 * always has a wall behind it. Scenery from a stage bank -
                 * a distant block of buildings painted as one card - has
                 * nothing behind it by definition, so the ray misses every
                 * time and the card is hung an arm's length from the face.
                 * At 2.3 m a head movement of thirty centimetres swings it
                 * across a quarter of the view, which is buildings sliding
                 * about when you lean; a real building three hundred metres
                 * off would not move by a pixel. Nothing else in the scene
                 * can do that: exact geometry carries its true distance, and
                 * at true distance there is no parallax left to see.
                 * So judge by size. A splash is tens of pixels across; a
                 * backdrop is hundreds. Anything wider than sprmissfar goes
                 * out to sprfar with the sky, where it belongs. */
                float wpx = sx[1] - sx[0], hpx = sy[2] - sy[0];
                if (wpx < 0) wpx = -wpx;
                if (hpx < 0) hpx = -hpx;
                if (wpx >= (float)g_sprMissFar || hpx >= (float)g_sprMissFar) {
                    dist = g_sprFar;
                    g_bigMiss++;
                }
            }
            g_splashHits++;
        }
    /* THE OVERLAY IS LAID OUT FOR A 60 DEGREE WINDOW. The ammo drum sits in
     * the corner of the game's frame, which in a headset is barely 25 degrees
     * off centre - the middle of the view, not its edge, which is why the car
     * chase dashboard floats in front of your face instead of sitting on the
     * bottom rail. hudspread pushes every overlay sprite away from the centre
     * by that percent, hudscale sets its size independently, so the drum can
     * go out to the periphery without swelling. Sprites that belong to the
     * world - the crosshair, hit splashes, the sky - are angles the game
     * computed and are never touched. */
    {
    if (!panel && !world && !back && (g_hudSpread != 100 || g_hudScale != 100)) {
        float mx = (sx[0] + sx[2]) * 0.5f, my = (sy[0] + sy[2]) * 0.5f;
        float sp = (float)g_hudSpread / 100.0f, sc = (float)g_hudScale / 100.0f;
        float nx = g_cx + (mx - g_cx) * sp, ny = g_cy + (my - g_cy) * sp;
        for (i = 0; i < 4; i++) {
            sx[i] = nx + (sx[i] - mx) * sc;
            sy[i] = ny + (sy[i] - my) * sc;
        }
    }
    /* The dashboard is not HUD and it is not scenery: it is the car you are
     * sitting in. Spreading it to the periphery with the rest of the overlay
     * is wrong - it belongs low and near, under the line of sight, where a
     * real dashboard is. So it gets its own placement: its own distance, its
     * own drop below the centre and its own size, and it is the ONE overlay
     * group hudspread does not touch. paneldrop is in the game's own screen
     * pixels, which is the same measure the sprite arrived in - 60 is a
     * quarter of the way down the 480 line frame. */
    if (panel) {
        float mx = (sx[0] + sx[2]) * 0.5f, my = (sy[0] + sy[2]) * 0.5f;
        float sc = (float)g_panelScale / 100.0f;
        float ny = my + (float)g_panelDrop;
        for (i = 0; i < 4; i++) {
            sx[i] = mx + (sx[i] - mx) * sc;
            sy[i] = ny + (sy[i] - my) * sc;
        }
        if (g_panelDist > 0) dist = (float)g_panelDist;
    }
    }
    if (!back && dist == g_sprDist && prio != 0) {
        float w2 = sx[1] - sx[0], h2 = sy[2] - sy[0];
        if (w2 < 0) w2 = -w2;
        if (h2 < 0) h2 = -h2;
        g_farSpr++;
        if (w2 * h2 > g_farSprW * g_farSprH) {
            g_farSprW = w2; g_farSprH = h2; g_farSprTex = s[1];
        }
    }
    for (i = 0; i < 6; i++) {
        int k = order[i];
        static const int cx[4] = { 0, 1, 1, 0 };
        static const int cy[4] = { 0, 0, 1, 1 };
        g_build[g_buildCount].x =  (sx[k] - g_cx) * dist / ffx;
        g_build[g_buildCount].y = -(sy[k] - g_cy) * dist / ffy;
        g_build[g_buildCount].z = -dist;
        g_build[g_buildCount].col = col;
        g_build[g_buildCount].u = cx[k] ? tr->u1 : tr->u0;
        g_build[g_buildCount].v = cy[k] ? tr->v1 : tr->v0;
        g_build[g_buildCount].d = back ? 0.0f : 1.0f;
        g_buildCount++;
    }
    }
}

/* The backdrop reaches us as flat screen rectangles that end on the horizon.
 * A rectangle is exactly as wide as the game's own 60 degree frame, so in a
 * headset it stops where the frame stops. Instead of laying it flat, bend it:
 * every screen x becomes a yaw of atan((x-320)/fx) on a cylinder of radius
 * sprfar, and the whole panorama is repeated left and right so that turning
 * the head finds sky rather than a void. Heights keep the same tangent
 * relation, so the horizon stays where the game put it. */
static void pushSkyDome(void)
{
    float lo = 1e9f, hi = -1e9f, span;
    int t, rep, seg;
    DWORD col;

    g_domeQ = 0; g_domeSkip = 0;
    g_domeWalk[0] = g_domeWalk[1] = 0;
    g_skyHeld = 0;
    if (g_skyN) {
        g_skyMiss = 0;
    } else {
        const TexReg *hold;
        if (!g_skyHold || !g_skyHoldOk || !g_skyLocked || g_skyRing < 2) return;
        if (g_skyMiss < 1000000) g_skyMiss++;
        if (g_skyMiss > g_skyHold) return;
        hold = regFind(g_skyLockTex);
        if (!hold) return;
        /* one synthetic tile, wide enough to be taken for a panorama and
         * carrying the id the ring is keyed on. Everything the locked path
         * actually uses - the ring length, the phase, the two tangents - is
         * remembered already; x and y here exist only to get past the "is this
         * a backdrop or a full screen picture" test above. */
        g_sky[0].tex = g_skyLockTex;
        g_sky[0].x0 = 0.0f;   g_sky[0].x1 = 641.0f;
        g_sky[0].y0 = g_cy - g_skyTanT * g_fy;
        g_sky[0].y1 = g_cy - g_skyTanB * g_fy;
        g_sky[0].sh[0] = g_skyHoldSh[0];
        g_sky[0].sh[1] = g_skyHoldSh[1];
        g_sky[0].sh[2] = g_skyHoldSh[2];
        g_skyN = 1;
        g_skyHeld = 1;
    }
    for (t = 0; t < g_skyN; t++) {
        if (g_sky[t].x0 < lo) lo = g_sky[t].x0;
        if (g_sky[t].x1 > hi) hi = g_sky[t].x1;
    }
    span = hi - lo;
    if (span < 1.0f) return;
    /* Deciding backdrop against full screen picture by width alone broke the
     * moment the camera turned and only ONE of the two panorama tiles was
     * still on screen: 584 points wide, judged a picture, drawn flat right in
     * front of the eyes - a rectangle of sky punched through a wall. Width is
     * only ever evidence FOR the panorama, never against it, so remember the
     * textures once they have been seen in one; and a tile that starts well
     * above the top of the frame is scenery whatever its width. */
    for (t = 0; t < g_skyN; t++)
        if (span > 640.0f || g_sky[t].y0 < -50.0f) skyTexRemember(g_sky[t].tex);
    /* the widest panorama ever seen is the true period to repeat by: with one
     * tile left on screen the span shrinks to that tile and the sky would
     * start repeating twice as often as it should */
    if (span > g_skySpan) g_skySpan = span;
    {
        int known = 0;
        for (t = 0; t < g_skyN; t++) if (skyTexKnown(g_sky[t].tex)) known = 1;
        if (!known && span <= 640.0f) {
        /* a single rectangle no wider than the frame is not scenery - it is a
         * full screen picture, like the AM2 logo on the way in. Those stay
         * flat and close, or they end up wrapped around the room. */
        for (t = 0; t < g_skyN; t++) {
            DWORD s2[24];
            ZeroMemory(s2, sizeof(s2));
            s2[1] = g_sky[t].tex;
            *(float *)&s2[3] = g_sky[t].x0;
            *(float *)&s2[4] = g_sky[t].y0;
            *(float *)&s2[7] = g_sky[t].x1;
            *(float *)&s2[8] = g_sky[t].y1;
            s2[6] = 2;                     /* overlay, behind the real HUD */
            s2[19] = (DWORD)(int)g_sky[t].sh[0];
            s2[20] = (DWORD)(int)g_sky[t].sh[1];
            s2[21] = (DWORD)(int)g_sky[t].sh[2];
            pushSprite(s2);
        }
        return;
        }
    }

    /* ------------------------------------------------- the panorama, whole
     * The backdrop is a ring of equal-width tiles. Only the two or three that
     * face the camera are submitted in any one frame, and the old code drew
     * just those, repeated by the widest span it had ever seen. When the ring
     * turned out to be three tiles wide and only two were on screen, the
     * period stayed three tiles and the missing one came out as a black
     * rectangle standing on the horizon - the "doors" in the sky.
     * So learn the ring instead: whenever two tiles arrive edge to edge,
     * remember that one follows the other. After that the whole circle can be
     * drawn every frame from the one tile that happens to be visible, walking
     * the chain forwards and backwards. Nothing is invented - every texture
     * drawn is one the game has shown in this very panorama. */
    {
        int idx[8], n = g_skyN, i2, j2;
        for (i2 = 0; i2 < n; i2++) idx[i2] = i2;
        for (i2 = 0; i2 < n - 1; i2++)          /* sort by left edge */
            for (j2 = i2 + 1; j2 < n; j2++)
                if (g_sky[idx[j2]].x0 < g_sky[idx[i2]].x0) {
                    int sw = idx[i2]; idx[i2] = idx[j2]; idx[j2] = sw;
                }
        for (i2 = 0; i2 + 1 < n; i2++) {
            float gap = g_sky[idx[i2]].x1 - g_sky[idx[i2 + 1]].x0;
            if (gap < -4.0f || gap > 4.0f) continue;
            skyLink(g_sky[idx[i2]].tex, g_sky[idx[i2 + 1]].tex);
        }
        t = idx[0];                              /* the anchor tile */
    }
    g_skyLockedFwd = 0;
    {
        const TexReg *anchor = regFind(g_sky[t].tex);
        float aL, aR, w1, yt, yb;
        int rep, seg, reps;
        if (!anchor) { g_capHave = 0; return; }
        {
            int c, ch[3];
            float sh[3];
            /* the sky is a flat sprite in the game and takes no light; the
             * muzzle flash used to paint the whole dome white */
            sh[0] = g_sky[t].sh[0] + (g_skyAmb ? (float)g_amb[0] : 0.0f);
            sh[1] = g_sky[t].sh[2] + (g_skyAmb ? (float)g_amb[2] : 0.0f);
            sh[2] = g_sky[t].sh[1] + (g_skyAmb ? (float)g_amb[1] : 0.0f);
            for (c = 0; c < 3; c++) {
                int v = g_doShade ? (int)(sh[c] + 255.0f) : 255;
                v = v * (int)g_texGain / 100;
                if (v < 0) v = 0;
                if (v > 255) v = 255;
                ch[c] = v;
            }
            col = ((DWORD)(g_alphaMode == 1 ? 0x00 :
                           g_alphaMode == 2 ? 0xC0 : 0x40) << 24) |
                  ((DWORD)ch[2] << 16) | ((DWORD)ch[1] << 8) | (DWORD)ch[0];
        }
        /* pixels are not angles: convert the tile edges once, then step by
         * the tile's own angular width all the way round */
        /* WHERE THE FLOATING CAME FROM. The tile's angular width was measured
         * as atan(x1/fx) - atan(x0/fx): through the LIVE focal length, and
         * through a tangent. Both are wrong for a panorama.
         *  - fx is not constant. The game zooms for distant fights (the log
         *    shows it swinging 1046 to 1345), so the tile's width, and with
         *    it the whole dome, was rescaling every time the camera zoomed.
         *  - the panorama is a scrolling blit, not geometry: the game slides
         *    it linearly with yaw. Placing it by a tangent makes a feature
         *    sit right at the centre of the screen and drift as it moves out
         *    towards the edge - the sky sliding against the buildings.
         * Once the ring has closed, none of that has to be measured: N tiles
         * go round, so a tile is 360/N wide, full stop, and screen x maps to
         * yaw linearly, anchored where the two agree - the centre. The dome
         * then does not depend on fx at all. Until the ring closes there is
         * nothing to anchor to and the old estimate stands. */
        /* WHAT WENT WRONG BOTH TIMES. The tile's bearing was measured off the
         * screen: first through atan and the LIVE focal length, which the
         * game changes on every zoom, so the dome rescaled; then through the
         * tile's own pixel width, which is worse, because the game clips the
         * sprite at the screen edge - a 762 point tile arrives 584 points
         * wide with no way to tell from the outside - and dividing by a width
         * that jumps sends the bearing flying. The screen cannot answer this
         * question. The view matrix can: the panorama is a fixed ring in the
         * world, so measure it ONCE, remember the world bearing, and after
         * that place it from the matrix, which is the same thing the walls
         * are placed by. Then it is nailed to the world by construction. */
        aL = (float)atan(((double)g_sky[t].x0 - (double)g_cx) / g_fx);
        aR = (float)atan(((double)g_sky[t].x1 - (double)g_cx) / g_fx);
        w1 = aR - aL;
        {
            int ring = skyRingLen(g_sky[t].tex);
            g_skyRing = ring;
            if (!g_skyLock || !g_upOk || ring < 2) {
                g_skyLocked = 0;
            } else if (g_skyLocked &&
                       skyIndexOf(g_skyLockTex, g_sky[t].tex, ring) >= 0) {
                /* still the panorama we locked onto */
            } else if (w1 > 0.02f) {
                float d = g_camRightAz - g_camAz;
                while (d >  3.14159265f) d -= 6.28318531f;
                while (d < -3.14159265f) d += 6.28318531f;
                g_skyLockTex = g_sky[t].tex;
                g_skyPhase   = g_camAz + (d >= 0.0f ? aL : -aL);
                g_skyTanT    = (g_cy - g_sky[t].y0) / g_fy;
                g_skyTanB    = (g_cy - g_sky[t].y1) / g_fy;
                g_skyLocked  = 1;
                /* How many tiles go round is 360 degrees divided by the tile's
                 * own measured angular width (w1 here is aR - aL, before it is
                 * overwritten below). The successor chain only says WHICH tile
                 * follows which; when the game has shown just two and scrolled
                 * them past each other the chain closes on a false 2-cycle and
                 * ring == 2, which would set the width to 180 degrees. Measure
                 * it instead, and repeat the known tiles round at true scale. */
                {
                    int rd = (int)(6.28318531f / w1 + 0.5f);
                    if (rd < 4)  rd = 4;
                    if (rd > 36) rd = 36;
                    g_skyRingDraw = rd;
                }
            }
            if (g_skyLocked) w1 = 6.28318531f / (float)g_skyRingDraw;
            g_skyLockedFwd = g_skyLocked;
            if (g_skyLocked && !g_skyHeld) {   /* remember it for the frames
                                                * the game does not blit it */
                g_skyHoldSh[0] = g_sky[t].sh[0];
                g_skyHoldSh[1] = g_sky[t].sh[1];
                g_skyHoldSh[2] = g_sky[t].sh[2];
                g_skyHoldOk = 1;
            }
        }
        if (w1 < 0.02f) { g_capHave = 0; return; }
        if (g_skyLocked) {
            yt = g_skyTanT * g_sprFar;
            yb = g_skyTanB * g_sprFar;
        } else {
            yt = (g_cy - g_sky[t].y0) / g_fy * g_sprFar;
            yb = (g_cy - g_sky[t].y1) / g_fy * g_sprFar;
        }
        g_capY = yt;
        g_capCol = 0x40000000u |
                   ((DWORD)(int)anchor->top[2] << 16) |
                   ((DWORD)(int)anchor->top[1] << 8) |
                   (DWORD)(int)anchor->top[0];
        g_capHave = 1;
        /* a closed ring is drawn exactly once round; an open chain still has
         * to be repeated left and right to fill the circle */
        reps = g_skyLocked ? g_skyRingDraw : (int)(3.1416f / w1) + 2;
        if (reps > 40) reps = 40;
        for (rep = g_skyLocked ? 0 : -reps; rep <= reps; rep++) {
            const TexReg *tr;
            float base;
            if (g_skyLocked) {
                if (rep >= g_skyRingDraw) break;     /* once round, no more */
                tr = regFind(skyWalk(g_skyLockTex, rep));
                /* a bearing in the WORLD. The frame it is built in turns with
                 * the camera because its axes are read out of the matrix, so
                 * this number never has to change again. */
                base = g_skyPhase + (float)rep * w1;
            } else {
                tr = regFind(skyWalk(g_sky[t].tex, rep));
                base = aL + (float)rep * w1;
            }
            if (rep >= 0 && rep < 2)
                g_domeWalk[rep] = g_skyLocked ? skyWalk(g_skyLockTex, rep)
                                              : skyWalk(g_sky[t].tex, rep);
            if (!tr) {
                g_domeSkip++;
                /* skydebug draws the band flat, so a missing texture stops
                 * being a reason not to draw it - which is the whole point:
                 * it tells apart "nothing was emitted" from "it was emitted
                 * somewhere you cannot see" */
                if (!g_skyDebug) continue;
            }
            for (seg = 0; seg < g_skySeg; seg++) {
                float fa = (float)seg / (float)g_skySeg;
                float fb = (float)(seg + 1) / (float)g_skySeg;
                /* tr may be NULL here: skydebug keeps drawing the ring
                 * step whose texture the chain could not find */
                float ua = tr ? tr->u0 + (tr->u1 - tr->u0) * fa : 0.0f;
                float ub = tr ? tr->u0 + (tr->u1 - tr->u0) * fb : 0.0f;
                float ta = base + w1 * fa, tb = base + w1 * fb;
                float ca = (float)cos(ta), sa2 = (float)sin(ta);
                float cb = (float)cos(tb), sb2 = (float)sin(tb);
                float px[4], py[4], pz[4], uu[4], vv[4];
                int i, order[6] = { 0, 1, 2, 0, 2, 3 };
                float up[3], fwd[3], rgt[3];
                if (g_buildCount + 12 > MAX_QUADS * 6) return;
                /* the cylinder stands on the world's vertical, not the
                 * view's - see upFrame. Level camera: fwd = (0,0,-1),
                 * rgt = (1,0,0), and this is the old expression verbatim.
                 * Locked, the ring turns about world +Z instead, so a bearing
                 * means the same thing this frame as it did last frame. */
                skyFrame(up, fwd, rgt);
                for (i = 0; i < 4; i++) {
                    float c2 = (i == 1 || i == 2) ? cb : ca;
                    float s3 = (i == 1 || i == 2) ? sb2 : sa2;
                    float yy = (i < 2) ? yt : yb;
                    px[i] = g_sprFar * (fwd[0]*c2 + rgt[0]*s3) + up[0]*yy;
                    py[i] = g_sprFar * (fwd[1]*c2 + rgt[1]*s3) + up[1]*yy;
                    pz[i] = g_sprFar * (fwd[2]*c2 + rgt[2]*s3) + up[2]*yy;
                }
                if (g_skyDebug || !tr) {
                    /* flat magenta, no texture at all: if this is not on the
                     * screen then the geometry is not on the screen */
                    uu[0] = uu[1] = uu[2] = uu[3] = -1.0f;
                    vv[0] = vv[1] = vv[2] = vv[3] = -1.0f;
                    col = 0x40FF00FFu;
                } else {
                    uu[0] = uu[3] = ua; uu[1] = uu[2] = ub;
                    vv[0] = vv[1] = tr->v0; vv[2] = vv[3] = tr->v1;
                }
                if (g_buildCount / 6 < MAX_QUADS)
                    g_quadKey[g_buildCount / 6] = 0xFFFFFFFFFull;
                for (i = 0; i < 6; i++) {
                    int k = order[i];
                    g_build[g_buildCount].x = px[k];
                    g_build[g_buildCount].y = py[k];
                    g_build[g_buildCount].z = pz[k];
                    g_build[g_buildCount].col = col;
                    g_build[g_buildCount].u = uu[k];
                    g_build[g_buildCount].v = vv[k];
                    g_build[g_buildCount].d = 0.0f;
                    g_buildCount++;
                }
                g_domeQ++;
                /* The cap is built on the SAME segment edges as the panorama
                 * it sits on. Drawn as its own coarse 32-sided ring it shared
                 * no vertices with the fine one below, and the mismatched
                 * chords let the background through as a thin dark arc across
                 * the sky - the seam. Sharing the edges makes it watertight. */
                if (g_skyCap) {
                    float yz = yt + g_sprFar * 2.0f;
                    if (g_buildCount / 6 < MAX_QUADS)
                        g_quadKey[g_buildCount / 6] = 0xFFFFFFFFFull;
                    /* apex on the same axis the ring turns about */
                    px[2] = up[0]*yz; py[2] = up[1]*yz; pz[2] = up[2]*yz;
                    px[3] = px[2];    py[3] = py[2];    pz[3] = pz[2];
                    px[0] = g_sprFar * (fwd[0]*ca + rgt[0]*sa2) + up[0]*yt;
                    py[0] = g_sprFar * (fwd[1]*ca + rgt[1]*sa2) + up[1]*yt;
                    pz[0] = g_sprFar * (fwd[2]*ca + rgt[2]*sa2) + up[2]*yt;
                    px[1] = g_sprFar * (fwd[0]*cb + rgt[0]*sb2) + up[0]*yt;
                    py[1] = g_sprFar * (fwd[1]*cb + rgt[1]*sb2) + up[1]*yt;
                    pz[1] = g_sprFar * (fwd[2]*cb + rgt[2]*sb2) + up[2]*yt;
                    for (i = 0; i < 6; i++) {
                        int k = order[i];
                        g_build[g_buildCount].x = px[k];
                        g_build[g_buildCount].y = py[k];
                        g_build[g_buildCount].z = pz[k];
                        g_build[g_buildCount].col = g_capCol;
                        g_build[g_buildCount].u = -1.0f;
                        g_build[g_buildCount].v = -1.0f;
                        g_build[g_buildCount].d = 0.0f;
                        g_buildCount++;
                    }
                    g_domeQ++;
                }
            }
        }
    }
    g_capHave = 0;
}

/* ------------------------------------------------------------ ground fill
 * Say plainly what this is: INVENTED GEOMETRY. The game has no ground outside
 * the chunk it is drawing, so past the last object list there is nothing at
 * all, and nothing is black. This lays a flat slab under the whole scene so
 * the void reads as road rather than as a hole. It is a backdrop, not data -
 * it will not match kerbs, it will not follow hills, and anything that leans
 * on it being real will be wrong. It exists so the view is bearable while the
 * real question - how much city can be made to arrive - is still open. */
static int   g_groundFill;
static int   g_groundCalls, g_groundEmitted, g_groundFail, g_groundHadTex;
/* The header comment said the camera sits 1030 units over the road. The probe
 * disagrees: take any ground quad (layer 6) and unproject it - sy 538 at depth
 * 8892, sy 1139 at 2792, sy 3105 at 860 - and all three land on y = -215 give
 * or take ten. So the slab was sitting eight hundred units below the road,
 * under the horizon, where nothing could see it. */
static float g_groundY = -215.0f;
static float g_groundSize = 60000.0f;
static LONG  g_groundTex = -1;
static DWORD g_groundCol = 0x00404448;
static float g_groundTile = 8.0f;

static void pushGround(void)
{
    const TexReg *tr = NULL;
    float h = g_groundSize;
    float px[4], py[4], pz[4], uu[4], vv[4];
    int i, order[6] = { 0, 1, 2, 0, 2, 3 };
    DWORD col;

    g_groundCalls++;
    if (!g_groundFill) return;
    if (g_buildCount + 6 > MAX_QUADS * 6) { g_groundFail = 1; return; }
    if (g_groundTex >= 0) tr = regFind((DWORD)g_groundTex);

    col = 0x40000000u | (g_groundCol & 0x00FFFFFFu);

    /* The slab is the road's plane, not the screen's. Built square to the
     * view it stayed level with the headset while the world tilted under it,
     * and its edge cut across the real horizon - grey over half the sky. Lay
     * it in the frame the world calls horizontal instead; with a level camera
     * this is the old (x, groundY, z) rectangle to the last bit. */
    {
        float up[3], fwd[3], rgt[3];
        static const float sgnA[4] = { -1.0f,  1.0f,  1.0f, -1.0f };   /* along right */
        static const float sgnB[4] = {  1.0f,  1.0f, -1.0f, -1.0f };   /* along fwd   */
        upFrame(up, fwd, rgt);
        for (i = 0; i < 4; i++) {
            float a = h * sgnA[i], b = h * sgnB[i];
            px[i] = rgt[0]*a + fwd[0]*b + up[0]*g_groundY;
            py[i] = rgt[1]*a + fwd[1]*b + up[1]*g_groundY;
            pz[i] = rgt[2]*a + fwd[2]*b + up[2]*g_groundY;
        }
    }
    if (tr) {
        float t = g_groundTile;
        uu[0] = tr->u0; vv[0] = tr->v0;
        uu[1] = tr->u0 + (tr->u1 - tr->u0) * t; vv[1] = tr->v0;
        uu[2] = tr->u0 + (tr->u1 - tr->u0) * t;
        vv[2] = tr->v0 + (tr->v1 - tr->v0) * t;
        uu[3] = tr->u0; vv[3] = tr->v0 + (tr->v1 - tr->v0) * t;
    } else {
        for (i = 0; i < 4; i++) { uu[i] = -1.0f; vv[i] = -1.0f; }
    }
    /* just in front of the sky and behind everything the game submitted */
    g_quadKey[g_buildCount / 6] = 0xFFFFFFFFEull;
    for (i = 0; i < 6; i++) {
        int k = order[i];
        g_build[g_buildCount].x = px[k];
        g_build[g_buildCount].y = py[k];
        g_build[g_buildCount].z = pz[k];
        g_build[g_buildCount].col = col;
        g_build[g_buildCount].u = uu[k];
        g_build[g_buildCount].v = vv[k];
        g_build[g_buildCount].d = 0.0f;
        g_buildCount++;
    }
    g_groundEmitted++;
    g_groundHadTex = (tr != NULL);
}

/* ------------------------------------------------------------- feet fill
 * INVENTED GEOMETRY, like the ground slab, but built from the real floor.
 * Where the camera stands the flat game never looks down, so the level data
 * holds no floor there - stage 3's mezzanine is the case: every list of the
 * section is in memory and the lobby still shows through under the feet.
 * Nothing can be learnt that was never modelled. This takes the nearest real
 * floor quad of the frame - flat, textured, a metre or three below the eye,
 * a plausible tile size - and lays copies of it along its own two edges until
 * feetfill metres around the eye are covered, a few centimetres LOWER than
 * the original, so wherever a real floor exists it wins and the copies only
 * show where there was nothing. Same texture, same shade, same sort layer,
 * radial keys like every other world quad. It cannot know a balcony edge from
 * a missing floor, so keep the radius small. */
static void pushFeetFill(void)
{
    float up[3], fwd[3], rgt[3], upm = g_unitsPerMetre;
    UINT nq, q, best = (UINT)-1;
    float bestD = 1e30f, bestH = 0.0f, R, drop;
    int k;
    static const int corner[4] = { 0, 1, 2, 5 };

    g_feetLog = 0;
    if (g_feetFill <= 0 || !g_passOn) return;
    nq = g_buildCount / 6;
    if (nq > MAX_QUADS) nq = MAX_QUADS;
    upFrame(up, fwd, rgt);
    R = (float)g_feetFill * upm;
    drop = (float)g_feetDrop * 0.01f * upm;

    for (q = 0; q < nq; q++) {
        const Vtx *v = &g_build[q * 6];
        float hmin = 1e30f, hmax = -1e30f, hm, c[3] = { 0, 0, 0 }, e1[3], e2[3], l1, l2, hu, hd;
        if (g_quadFlat[q]) continue;
        if (v[0].u < 0.0f) continue;                      /* untextured        */
        if (v[0].d <= 0.0f || v[0].d >= 1.0f) continue;   /* sky, overlay      */
        for (k = 0; k < 4; k++) {
            const Vtx *p = &v[corner[k]];
            float h = p->x * up[0] + p->y * up[1] + p->z * up[2];
            if (h < hmin) hmin = h;
            if (h > hmax) hmax = h;
            c[0] += p->x * 0.25f; c[1] += p->y * 0.25f; c[2] += p->z * 0.25f;
        }
        if (hmax - hmin > 0.03f * upm) continue;          /* not flat          */
        hm = (hmin + hmax) * 0.5f;
        if (hm > -0.9f * upm || hm < -3.5f * upm) continue;   /* not a floor under the feet */
        e1[0] = v[1].x - v[0].x; e1[1] = v[1].y - v[0].y; e1[2] = v[1].z - v[0].z;
        e2[0] = v[5].x - v[0].x; e2[1] = v[5].y - v[0].y; e2[2] = v[5].z - v[0].z;
        l1 = (float)sqrt((double)(e1[0]*e1[0] + e1[1]*e1[1] + e1[2]*e1[2]));
        l2 = (float)sqrt((double)(e2[0]*e2[0] + e2[1]*e2[1] + e2[2]*e2[2]));
        if (l1 < 0.8f * upm || l2 < 0.8f * upm || l1 > 16.0f * upm || l2 > 16.0f * upm) continue;
        hu = c[0] * up[0] + c[1] * up[1] + c[2] * up[2];
        c[0] -= up[0] * hu; c[1] -= up[1] * hu; c[2] -= up[2] * hu;
        hd = (float)sqrt((double)(c[0]*c[0] + c[1]*c[1] + c[2]*c[2])) -
             0.5f * (float)sqrt((double)(l1 * l1 + l2 * l2));
        if (hd < 0.0f) hd = 0.0f;
        if (hd < bestD) { bestD = hd; best = q; bestH = hm; }
    }
    if (best == (UINT)-1) return;
    g_feetLog = 1;
    g_feetLogH = -bestH / upm;
    {
        const Vtx *v = &g_build[best * 6];
        float e1[3], e2[3], c[3] = { 0, 0, 0 }, l1, l2, lim;
        int i1, i2, K1, K2, copies = 0;
        DWORD layer = g_quadLayerB[best];
        e1[0] = v[1].x - v[0].x; e1[1] = v[1].y - v[0].y; e1[2] = v[1].z - v[0].z;
        e2[0] = v[5].x - v[0].x; e2[1] = v[5].y - v[0].y; e2[2] = v[5].z - v[0].z;
        l1 = (float)sqrt((double)(e1[0]*e1[0] + e1[1]*e1[1] + e1[2]*e1[2]));
        l2 = (float)sqrt((double)(e2[0]*e2[0] + e2[1]*e2[1] + e2[2]*e2[2]));
        for (k = 0; k < 4; k++) {
            const Vtx *p = &v[corner[k]];
            c[0] += p->x * 0.25f; c[1] += p->y * 0.25f; c[2] += p->z * 0.25f;
        }
        K1 = (int)(R / l1) + 1; if (K1 > 12) K1 = 12;
        K2 = (int)(R / l2) + 1; if (K2 > 12) K2 = 12;
        lim = R + 0.5f * (l1 > l2 ? l1 : l2);
        for (i1 = -K1; i1 <= K1; i1++) {
            for (i2 = -K2; i2 <= K2; i2++) {
                float cc[3], hu, dh;
                DWORD kmax = 0;
                UINT at;
                if (!i1 && !i2) continue;
                cc[0] = c[0] + e1[0] * i1 + e2[0] * i2;
                cc[1] = c[1] + e1[1] * i1 + e2[1] * i2;
                cc[2] = c[2] + e1[2] * i1 + e2[2] * i2;
                hu = cc[0] * up[0] + cc[1] * up[1] + cc[2] * up[2];
                cc[0] -= up[0] * hu; cc[1] -= up[1] * hu; cc[2] -= up[2] * hu;
                dh = (float)sqrt((double)(cc[0]*cc[0] + cc[1]*cc[1] + cc[2]*cc[2]));
                if (dh > lim) continue;
                if (copies >= 96 || g_buildCount + 6 > MAX_QUADS * 6) break;
                at = g_buildCount;
                for (k = 0; k < 6; k++) {
                    Vtx *o = &g_build[at + k];
                    float px = v[k].x + e1[0] * i1 + e2[0] * i2 - up[0] * drop;
                    float py = v[k].y + e1[1] * i1 + e2[1] * i2 - up[1] * drop;
                    float pz = v[k].z + e1[2] * i1 + e2[2] * i2 - up[2] * drop;
                    DWORD wfull = layer * LAYER + radialKey((float)sqrt((double)(px*px + py*py + pz*pz)));
                    float dn = 1.0f - (float)wfull / 4194304.0f;
                    if (dn < 0.0f) dn = 0.0f;
                    if (dn > 1.0f) dn = 1.0f;
                    if (wfull > kmax) kmax = wfull;
                    o->x = px; o->y = py; o->z = pz;
                    o->col = v[k].col; o->u = v[k].u; o->v = v[k].v; o->d = dn;
                }
                g_quadKey[at / 6] = (unsigned __int64)kmax + 16;
                g_quadFlat[at / 6] = 0;
                g_quadLayerB[at / 6] = (unsigned char)layer;
                g_buildCount += 6;
                copies++;
            }
        }
        g_feetLogN += (DWORD)copies;
    }
}

/* Frustum rejection, PPJ2DD.EXE 0x00442500. Per polygon the game builds a
 * four bit outcode for every corner (0x004426D7..0x0044280F) - left, right,
 * top, bottom against 0 and the two limits at 0x52B8AC / 0x52B8B0 - and looks
 * the pairs up in the table at 0x0044DDC0 to throw away anything that falls
 * wholly off one side. The helper at 0x00442500 is the shortcut: it returns 1
 * when the polygon's centre is plainly on screen, and the caller then submits
 * without consulting the outcodes at all (0x004426CA). Making it return 1
 * always therefore disables the whole frustum reject and costs six bytes.
 * The near plane test (w <= 0 at 0x004425A5) and the backface test
 * (0x00444270) sit BEFORE this and are left alone - dropping those would
 * submit geometry behind the eye and inside-out walls. */
static const BYTE CULL_SIG[] = { 0x83,0xEC,0x04,0x53,0x56,0x8B,0x74,0x24,0x10,
                                 0x33,0xC9 };
static const BYTE CULL_FIX[] = { 0xB8,0x01,0x00,0x00,0x00,0xC3 };

/* the six places the polygon loop hands a quad to the renderer, as they sit
 * in a PPJ2DD.EXE that loaded at its own base. Whatever the image base turns
 * out to be, a return address caught in wrap_quad differs from one of these
 * by exactly the relocation, which is all we need to find the cull helper. */
static const DWORD CULL_RET[] = { 0x0044293B, 0x00444155, 0x0044302E,
                                  0x0044343B, 0x00443846, 0x00443C51 };
#define CULL_HELPER 0x00442500

/* our own six bytes, already sitting there from an earlier load of this DLL:
 * the game loads the renderer once to ask its name and then frees it, so the
 * second load starts with fresh globals but a game that is already patched. */
static int cullFixAt(const BYTE *p)
{
    int i;
    if (!p || IsBadReadPtr(p, sizeof(CULL_FIX))) return 0;
    for (i = 0; i < (int)sizeof(CULL_FIX); i++)
        if (p[i] != CULL_FIX[i]) return 0;
    return 1;
}

static int cullSigAt(const BYTE *p)
{
    int i;
    if (!p || IsBadReadPtr(p, sizeof(CULL_SIG))) return 0;
    for (i = 0; i < (int)sizeof(CULL_SIG); i++)
        if (p[i] != CULL_SIG[i]) return 0;
    return 1;
}

static int cullWrite(BYTE *p)
{
    DWORD old;
    int i;
    if (!VirtualProtect(p, sizeof(CULL_FIX), PAGE_EXECUTE_READWRITE, &old)) {
        g_cullState = 3;
        return 0;
    }
    for (i = 0; i < (int)sizeof(CULL_FIX); i++) p[i] = CULL_FIX[i];
    VirtualProtect(p, sizeof(CULL_FIX), old, &old);
    FlushInstructionCache(GetCurrentProcess(), p, sizeof(CULL_FIX));
    g_cullPatched = 1;
    g_cullState = 1;
    g_cullAt = (DWORD)(DWORD_PTR)p;
    return 1;
}

/* ---------------------------------------------------------------------------
 * The SECOND reject, and the one that actually decides how much city exists.
 *
 * 0x00440C00 walks the scenery list of the chunk of track the player is on.
 * Every entry is 0x14 bytes: +0x00 model, +0x04..+0x0C world position,
 * +0x10 low byte = flags, high byte = angular half size in 0xB6 units.
 *
 *   00440C40  cmp dword ptr [esi], 0      ; list ends on a null model
 *   00440C45  push esi ; call 0x00440A70  ; ask whether it is worth drawing
 *   00440C4E  test al, al
 *   00440C50  jne 0x00440C5D              ; al != 0  ->  skip this object
 *   00440C52  push [esi] ; call 0x004421F0
 *   00440C5D  esi += 0x14 ; loop while the next model is non-null
 *
 * 0x00440A70 is a per-object test, not a per-polygon one: it takes the object
 * position minus the camera position (0x004DB898/9C/A0), turns it into a
 * bearing with the atan2 helper at 0x00404E60, and rejects the object when
 * that bearing, widened by the object's own angular size, falls outside the
 * horizontal window around the camera heading at 0x004DB892 - plus a distance
 * cut for the entries whose flags have bits 2-3. Flag bit 4 means "never
 * reject". So: turn your head in VR and half the street stops being submitted
 * at all, one whole object at a time, long before the polygon-level frustum
 * test at 0x00442500 ever sees it.
 *
 * Returning 0 always - three bytes, xor al,al / ret - makes every object in
 * the chunk list draw regardless of where the camera looks or how far away it
 * is. Its other caller, 0x00440F80, gates a second draw path the same way.
 *
 * What this does NOT do, and it needs saying plainly: it does not conjure up
 * the rest of the city. The lists are per chunk of track (cursor 0x004CF81C,
 * advanced as 0x004DB8B8 counts up), so objects belonging to chunks the player
 * has not reached are not in the list being walked and no patch here will add
 * them. This removes the angular and distance reject inside the current chunk,
 * which is exactly what head turning needs, and nothing more. */
static const BYTE OCULL_SIG[] = { 0x83,0xEC,0x0C,0x53,0x56,0x57,0x8B,0x7C,
                                  0x24,0x1C,0x66,0x8B,0x77,0x10 };
static const BYTE OCULL_FIX[] = { 0x32,0xC0,0xC3 };
#define OCULL_FUNC 0x00440A70

static int ocullFixAt(const BYTE *p)
{
    int i;
    if (!p || IsBadReadPtr(p, sizeof(OCULL_FIX))) return 0;
    for (i = 0; i < (int)sizeof(OCULL_FIX); i++)
        if (p[i] != OCULL_FIX[i]) return 0;
    return 1;
}

static int ocullSigAt(const BYTE *p)
{
    int i;
    if (!p || IsBadReadPtr(p, sizeof(OCULL_SIG))) return 0;
    for (i = 0; i < (int)sizeof(OCULL_SIG); i++)
        if (p[i] != OCULL_SIG[i]) return 0;
    return 1;
}

static int ocullWrite(BYTE *p)
{
    DWORD old;
    int i;
    if (!VirtualProtect(p, sizeof(OCULL_FIX), PAGE_EXECUTE_READWRITE, &old)) {
        g_ocullState = 3;
        return 0;
    }
    for (i = 0; i < (int)sizeof(OCULL_FIX); i++) p[i] = OCULL_FIX[i];
    VirtualProtect(p, sizeof(OCULL_FIX), old, &old);
    FlushInstructionCache(GetCurrentProcess(), p, sizeof(OCULL_FIX));
    g_ocullPatched = 1;
    g_ocullState = 1;
    g_ocullAt = (DWORD)(DWORD_PTR)p;
    return 1;
}

/* same three steps as the polygon patch: recognise our own bytes from an
 * earlier load, then the address the file gives, then a scan of the image */
static void patchObjCull(BYTE *base, DWORD span)
{
    DWORD off;
    BYTE *hit = NULL;
    int found = 0;

    if (!g_noObjCull || g_ocullPatched || !base) return;
    if (ocullFixAt(base + (OCULL_FUNC - 0x00400000))) {
        g_ocullPatched = 1;
        g_ocullState = 1;
        g_ocullAt = (DWORD)(DWORD_PTR)(base + (OCULL_FUNC - 0x00400000));
        return;
    }
    if (ocullSigAt(base + (OCULL_FUNC - 0x00400000))) {
        ocullWrite(base + (OCULL_FUNC - 0x00400000));
        return;
    }
    if (!span) { g_ocullState = 2; return; }
    for (off = 0x1000; off + sizeof(OCULL_SIG) < span; off++) {
        if (IsBadReadPtr(base + off, 1)) { off += 0xFFF; continue; }
        if (base[off] != OCULL_SIG[0]) continue;
        if (!ocullSigAt(base + off)) continue;
        hit = base + off;
        if (++found > 1) break;
    }
    g_ocullFound = found;
    if (found == 1) ocullWrite(hit);
    else g_ocullState = 2;
}

/* -------------------------------------------------------------- more city
 * The scenery is streamed, not stored as one world. 0x004CF820 is an array of
 * pairs {near stream, far stream} for the current route, picked by section
 * index word 0x004CF818 (0x004409F0). Each stream is a run of 8-byte records
 * {object list, key}, and 0x00440D00 walks the cursor 0x004CF81C forward while
 * the record key equals the progress counter word 0x004DB8B8, then draws
 * exactly ONE list - the one the player is standing in. A record whose next
 * key reads -1 ends the section, at which point the section index steps and
 * the cursors are rebuilt.
 *
 * That is why the city ends in a black wall a street away, and why everything
 * vanishes at a checkpoint: nothing was culled, the lists simply were not
 * walked. No patch inside the visibility test can fix that.
 *
 * So take over the call at 0x00440D69 - the one that hands the current list to
 * 0x00440C00 - and after the original list, hand over the next few records of
 * the same stream as well. The records are already in memory; the models they
 * point at live in the stage DLL data, which is fully resident. Nothing is
 * being invented here, the game is simply asked to draw lists it was going to
 * draw a few seconds later anyway.
 *
 * Honest limits: this walks FORWARD in the current section only. It stops at
 * the section boundary, because past it the cursors belong to a different
 * stream and rebuilding them by hand would mean second-guessing 0x00440A10.
 * And a chunk the player has already driven through is behind the cursor, so
 * looking back still shows the black wall. */
#define CITY_CALL_RVA    0x00040D69
#define CITY_DRAW_RVA    0x00040C00
#define CITY_NEARCUR_RVA 0x000CF81C

/* mov eax,[0x004CF81C] / mov ecx,[eax] / push ecx / call */
static const BYTE CITY_SIG[] = { 0xA1,0x1C,0xF8,0x4C,0x00,0x8B,0x08,0x51 };

/* g_cityAhead: declared above, set in init(), default 2 */
static volatile LONG g_cityState;   /* 0 off, 1 patched, 2 not found, 3 denied */
static int      g_cityExtra;            /* lists actually added this frame    */
static int      g_cityShown;            /* the same, as of the last full frame */
static int      g_quadCap = 2900;       /* how many quads HGL_D3D may be given */
static int      g_quadSent, g_quadHeld, g_quadHeldShown, g_quadSentShown;
static void (__cdecl *g_cityOrig)(void *);
static DWORD  **g_cityCur;

static void __attribute__((force_align_arg_pointer)) __cdecl cityThunk(void *list)
{
    int n;
    DWORD *r;
    g_cityOrig(list);
    if (g_cityAhead <= 0 || !g_cityCur || !g_cityOrig) return;
    if (IsBadReadPtr(g_cityCur, 4)) return;
    r = *g_cityCur;
    for (n = 0; n < g_cityAhead; n++) {
        if (IsBadReadPtr(r, 16)) break;
        if ((LONG)r[3] == -1) break;    /* the section ends at this record */
        r += 2;
        if (!r[0]) break;
        if (IsBadReadPtr((void *)(DWORD_PTR)r[0], 4)) break;
        g_cityExtra++;
        g_cityOrig((void *)(DWORD_PTR)r[0]);
    }
}

static void patchCity(BYTE *base)
{
    BYTE *p;
    DWORD old;
    LONG rel;
    int i;

    if (g_cityAhead <= 0 || g_cityState || !base) return;
    p = base + CITY_CALL_RVA;
    if (IsBadReadPtr(p - 8, 13)) { g_cityState = 2; return; }
    for (i = 0; i < (int)sizeof(CITY_SIG); i++)
        if (p[-8 + i] != CITY_SIG[i]) { g_cityState = 2; return; }
    if (p[0] != 0xE8) { g_cityState = 2; return; }
    if ((BYTE *)(p + 5 + *(LONG *)(p + 1)) != base + CITY_DRAW_RVA) {
        g_cityState = 1;                /* already redirected by an earlier load */
        return;
    }
    g_cityOrig = (void (__cdecl *)(void *))(base + CITY_DRAW_RVA);
    g_cityCur  = (DWORD **)(base + CITY_NEARCUR_RVA);
    rel = (LONG)(LONG_PTR)((BYTE *)cityThunk - (p + 5));
    if (!VirtualProtect(p, 5, PAGE_EXECUTE_READWRITE, &old)) {
        g_cityState = 3;
        return;
    }
    *(LONG *)(p + 1) = rel;
    VirtualProtect(p, 5, old, &old);
    FlushInstructionCache(GetCurrentProcess(), p, 5);
    /* the game now calls into this module, so it must never be unloaded -
     * it loads the renderer twice and frees the first copy, and a freed
     * thunk is a crash with no explanation attached */
    {
        HMODULE keep = NULL;
        GetModuleHandleExA(0x00000001 /* PIN */ | 0x00000004 /* FROM_ADDRESS */,
                           (LPCSTR)(void *)cityThunk, &keep);
    }
    g_cityState = 1;
}

/* attempt one: where the file says it should be, then a scan of the image */
static void installJoyHook(BYTE *base);   /* light-gun joystick hook, see below */

static void patchCull(void)
{
    BYTE *base = (BYTE *)GetModuleHandleA(NULL);
    DWORD span = 0, off;
    BYTE *hit = NULL;
    int found = 0;

    if (!base) return;
    {
        IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)base;
        if (!IsBadReadPtr(dos, sizeof(*dos)) && dos->e_magic == 0x5A4D) {
            IMAGE_NT_HEADERS *nt = (IMAGE_NT_HEADERS *)(base + dos->e_lfanew);
            if (!IsBadReadPtr(nt, sizeof(*nt)) && nt->Signature == 0x00004550)
                span = nt->OptionalHeader.SizeOfImage;
        }
    }
    g_cullSpan = span;
    g_cullBase = (DWORD)(DWORD_PTR)base;
    patchObjCull(base, span);
    patchCity(base);
    installProjHook(base);
    installClipHook(base);
    patchBehind(base);
    installPassHooks(base);
    installJoyHook(base);
    if (!g_noCull || g_cullPatched) return;
    if (cullFixAt(base + (CULL_HELPER - 0x00400000))) {
        g_cullPatched = 1;
        g_cullState = 1;
        g_cullAt = (DWORD)(DWORD_PTR)(base + (CULL_HELPER - 0x00400000));
        return;
    }
    if (cullSigAt(base + (CULL_HELPER - 0x00400000))) {
        cullWrite(base + (CULL_HELPER - 0x00400000));
        return;
    }
    if (!span) { g_cullState = 2; return; }
    for (off = 0x1000; off + sizeof(CULL_SIG) < span; off++) {
        if (IsBadReadPtr(base + off, 1)) { off += 0xFFF; continue; }
        if (base[off] != CULL_SIG[0]) continue;
        if (!cullSigAt(base + off)) continue;
        hit = base + off;
        if (++found > 1) break;
    }
    g_cullFound = found;
    if (found == 1) cullWrite(hit);
    else g_cullState = 2;
}

/* attempt two, once the game has told us where it calls us back from: the
 * distance from any of the six known call sites to the helper is fixed, so a
 * live return address pins the helper down no matter where the image landed
 * or how the executable was repacked. */
static void patchCullFromRet(DWORD ra)
{
    int i;
    /* a live return address pins the relocation, which pins both targets */
    if (g_noObjCull && !g_ocullPatched) {
        for (i = 0; i < (int)(sizeof(CULL_RET) / sizeof(CULL_RET[0])); i++) {
            BYTE *p = (BYTE *)(DWORD_PTR)(ra - CULL_RET[i] + OCULL_FUNC);
            if (ocullFixAt(p)) {
                g_ocullPatched = 1;
                g_ocullState = 1;
                g_ocullAt = (DWORD)(DWORD_PTR)p;
                break;
            }
            if (ocullSigAt(p)) { ocullWrite(p); break; }
        }
    }
    if (!g_noCull || g_cullPatched) return;
    for (i = 0; i < (int)(sizeof(CULL_RET) / sizeof(CULL_RET[0])); i++) {
        BYTE *p = (BYTE *)(DWORD_PTR)(ra - CULL_RET[i] + CULL_HELPER);
        if (cullFixAt(p)) {
            g_cullPatched = 1;
            g_cullState = 1;
            g_cullAt = (DWORD)(DWORD_PTR)p;
            return;
        }
        if (cullSigAt(p)) { cullWrite(p); return; }
    }
}

/* --------------------------------------------------------------- D3D11 side */

static HWND                     g_hwnd;
static ID3D11Device            *g_dev;
static ID3D11DeviceContext     *g_ctx;
static IDXGISwapChain          *g_swap;
static ID3D11RenderTargetView  *g_rtv;
static ID3D11DepthStencilView  *g_dsv;
static ID3D11Buffer            *g_vb, *g_cb;
static ID3D11VertexShader      *g_vs;
static ID3D11PixelShader       *g_ps;
static ID3D11InputLayout       *g_il;
static ID3D11RasterizerState   *g_rsSolid, *g_rsWire;
static ID3D11DepthStencilState *g_dss;
static ID3D11Texture2D          *g_pvAtlTex;
static ID3D11ShaderResourceView *g_pvAtlSRV;
static ID3D11SamplerState       *g_pvSamp;
static ID3D11BlendState         *g_pvBlendAdd;
static ID3D11DepthStencilState  *g_pvDssNo;
static int   g_wire;
static float g_yaw, g_pitch, g_ox, g_oy, g_oz;
static BOOL  g_drag;
static float g_speed = 800.0f;
static UINT  g_lastQuads;
static UINT  g_lastTexQuads;
static POINT g_dragFrom;

/* same contract as the VR shader: u < 0 = flat colour; textured vertices
 * carry shading with 0x80 neutral, hence tex * colour * 2 */
static const char *SHADER_SRC =
"cbuffer C : register(b0) { row_major float4x4 mvp; };\n"
"Texture2D atlas : register(t0); SamplerState smp : register(s0);\n"
"struct VIn  { float3 p : POSITION; float4 c : COLOR; float2 t : TEXCOORD0; float d : TEXCOORD1; };\n"
"struct VOut { float4 p : SV_POSITION; float4 c : COLOR; float2 t : TEXCOORD0; float d : TEXCOORD1; };\n"
"struct POut { float4 c : SV_TARGET; float d : SV_Depth; };\n"
"VOut vs(VIn i) { VOut o; o.p = mul(mvp, float4(i.p,1)); o.c = i.c; o.t = i.t; o.d = i.d; return o; }\n"
"POut ps(VOut i) {\n"
"    POut o;\n"
"    float4 s = atlas.Sample(smp, i.t);\n"
"    bool flat = i.t.x < -0.5;\n"
"    clip((flat ? 1.0 : s.a) - i.c.a);\n"
"    float3 rgb = flat ? i.c.rgb : saturate(s.rgb * i.c.rgb);\n"
"    o.c = float4(rgb, 1);\n"
"    o.d = i.d;\n"
"    return o;\n"
"}\n";

static void matIdent(float *m)
{
    int i;
    for (i = 0; i < 16; i++) m[i] = 0.0f;
    m[0] = m[5] = m[10] = m[15] = 1.0f;
}

static void matMul(const float *a, const float *b, float *o)
{
    int r, c, k;
    float t[16];
    for (r = 0; r < 4; r++)
        for (c = 0; c < 4; c++) {
            float s = 0.0f;
            for (k = 0; k < 4; k++) s += a[r * 4 + k] * b[k * 4 + c];
            t[r * 4 + c] = s;
        }
    for (r = 0; r < 16; r++) o[r] = t[r];
}

/* The preview window started as a debugging view and is now the second
 * player's screen: he holds the other controller, watches this on the monitor
 * and shoots what he sees. So it has to behave like the game's camera, not
 * like a free-flying inspector - which means following the game's own field of
 * view, including the cinematic narrowing it does for distant fights
 * (0x004DB8A4, 60 degrees down to about 18). g_projFov already carries that,
 * read live out of the EXE every frame by readProjection.
 *
 * previewzoom then magnifies on top, because a 640x480 window across the room
 * is a much smaller target than a headset. */
static void buildMVP(float *out)
{
    float view[16], proj[16], rotY[16], rotX[16], trans[16], tmp[16];
    float fovY = 1.20f;                    /* ~69 degrees, generous on purpose */
    float aspect = (float)g_winW / (float)g_winH;
    float zn = 20.0f, zf = 400000.0f;
    if (g_pvFollow && g_projOk) {
        /* the game's horizontal fov, turned into a vertical one for this
         * window's aspect, then magnified by previewzoom */
        float half = (float)(g_projFov * 3.14159265358979 / 360.0);
        float t = tanf(half) / (aspect > 0.01f ? aspect : 1.0f) * (4.0f / 3.0f);
        t /= (float)g_pvZoom / 100.0f;
        fovY = 2.0f * atanf(t);
        if (fovY < 0.05f) fovY = 0.05f;
        if (fovY > 2.8f)  fovY = 2.8f;
    }
    {
    float f = 1.0f / tanf(fovY * 0.5f);
    float cy = cosf(g_yaw), sy = sinf(g_yaw);
    float cx = cosf(g_pitch), sx = sinf(g_pitch);

    matIdent(trans);
    trans[3] = -g_ox; trans[7] = -g_oy; trans[11] = -g_oz;

    matIdent(rotY);
    rotY[0] = cy;  rotY[2] = -sy;
    rotY[8] = sy;  rotY[10] = cy;

    matIdent(rotX);
    rotX[5] = cx;  rotX[6] = sx;
    rotX[9] = -sx; rotX[10] = cx;

    matMul(rotX, rotY, tmp);
    matMul(tmp, trans, view);

    matIdent(proj);
    proj[0] = f / aspect;
    proj[5] = f;
    proj[10] = zn / (zf - zn);      /* reversed depth, see vc2vr.c */
    proj[11] = zf * zn / (zf - zn);
    proj[14] = -1.0f;
    proj[15] = 0.0f;

    matMul(proj, view, out);
    }
}

__attribute__((unused)) static void releaseTargets(void)
{
    if (g_rtv) { ID3D11RenderTargetView_Release(g_rtv); g_rtv = NULL; }
    if (g_dsv) { ID3D11DepthStencilView_Release(g_dsv); g_dsv = NULL; }
}

static BOOL makeTargets(void)
{
    ID3D11Texture2D *back = NULL, *depth = NULL;
    D3D11_TEXTURE2D_DESC dd;
    HRESULT hr;

    hr = IDXGISwapChain_GetBuffer(g_swap, 0, &IID_ID3D11Texture2D, (void **)&back);
    if (FAILED(hr)) return FALSE;
    ID3D11Device_CreateRenderTargetView(g_dev, (ID3D11Resource *)back, NULL, &g_rtv);
    ID3D11Texture2D_Release(back);

    ZeroMemory(&dd, sizeof(dd));
    dd.Width = g_winW; dd.Height = g_winH;
    dd.MipLevels = 1; dd.ArraySize = 1;
    dd.Format = DXGI_FORMAT_D32_FLOAT;
    dd.SampleDesc.Count = 1;
    dd.Usage = D3D11_USAGE_DEFAULT;
    dd.BindFlags = D3D11_BIND_DEPTH_STENCIL;
    if (FAILED(ID3D11Device_CreateTexture2D(g_dev, &dd, NULL, &depth))) return FALSE;
    ID3D11Device_CreateDepthStencilView(g_dev, (ID3D11Resource *)depth, NULL, &g_dsv);
    ID3D11Texture2D_Release(depth);
    return TRUE;
}

/* Borderless full screen on the monitor the window is on. want < 0 toggles.
 * The second player needs the whole screen, not a 1280x720 pane. */
static void pvFullScreen(HWND h, int want)
{
    static WINDOWPLACEMENT saved = { sizeof(saved) };
    static LONG savedStyle;
    static int on;
    if (want < 0) want = !on;
    if (want == on) return;
    if (want) {
        MONITORINFO mi = { sizeof(mi) };
        HMONITOR mon = MonitorFromWindow(h, MONITOR_DEFAULTTONEAREST);
        savedStyle = GetWindowLongA(h, GWL_STYLE);
        GetWindowPlacement(h, &saved);
        if (!GetMonitorInfoA(mon, &mi)) return;
        SetWindowLongA(h, GWL_STYLE, (savedStyle & ~WS_OVERLAPPEDWINDOW) | WS_POPUP);
        SetWindowPos(h, NULL, mi.rcMonitor.left, mi.rcMonitor.top,
                     mi.rcMonitor.right - mi.rcMonitor.left,
                     mi.rcMonitor.bottom - mi.rcMonitor.top,
                     SWP_NOZORDER | SWP_NOACTIVATE | SWP_FRAMECHANGED);
    } else {
        SetWindowLongA(h, GWL_STYLE, savedStyle);
        SetWindowPlacement(h, &saved);
        SetWindowPos(h, NULL, 0, 0, 0, 0,
                     SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE |
                     SWP_FRAMECHANGED);
    }
    on = want;
}

static LRESULT CALLBACK wndProc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_LBUTTONDOWN:
        g_drag = TRUE; g_dragFrom.x = LOWORD(l); g_dragFrom.y = HIWORD(l);
        SetCapture(h);
        return 0;
    case WM_LBUTTONUP:
        g_drag = FALSE; ReleaseCapture();
        return 0;
    case WM_MOUSEMOVE:
        if (g_drag) {
            int x = (short)LOWORD(l), y = (short)HIWORD(l);
            g_yaw   += (x - g_dragFrom.x) * 0.005f;
            g_pitch += (y - g_dragFrom.y) * 0.005f;
            g_dragFrom.x = x; g_dragFrom.y = y;
        }
        return 0;
    case WM_MOUSEWHEEL: {
        short d = (short)HIWORD(w);
        g_speed *= (d > 0) ? 1.4f : 0.71f;
        if (g_speed < 10.0f) g_speed = 10.0f;
        if (g_speed > 200000.0f) g_speed = 200000.0f;
        return 0;
    }
    case WM_KEYDOWN: {
        float step = g_speed;
        float cy = cosf(g_yaw), sy = sinf(g_yaw);
        if (w == 'W') { g_ox -= sy * step; g_oz -= cy * step; }
        if (w == 'S') { g_ox += sy * step; g_oz += cy * step; }
        if (w == 'D') { g_ox += cy * step; g_oz -= sy * step; }
        if (w == 'A') { g_ox -= cy * step; g_oz += sy * step; }
        if (w == 'R') { g_yaw = g_pitch = 0.0f; g_ox = g_oy = g_oz = 0.0f; }
        if (w == 'F') g_wire = !g_wire;
        if (w == 'T') InterlockedExchange(&g_uvOrder, (g_uvOrder + 1) & 7);
        if (w == 'G') InterlockedExchange(&g_texGain,
                          g_texGain >= 400 ? 25 : g_texGain + 25);
        if (w == 'U') InterlockedExchange(&g_neutral, !g_neutral);
        if (w == 'A') InterlockedExchange(&g_showAtlas, !g_showAtlas);
        if (w == 'P') g_probeAt = GetTickCount() + 5000;   /* fire in 5 s */
        if (w == 'C') InterlockedExchange(&g_calib, !g_calib);
        if (w == '3') g_skip3 = (g_skip3 + 1) % 3;
        if (w == 'Z') InterlockedExchange(&g_zflip, !g_zflip);
        if (w == 'K') InterlockedExchange(&g_alphaMode, (g_alphaMode + 1) % 3);
        if (w == 'W') { g_wcOn = !g_wcOn; if (!g_wcOn) wcReset(); }
        if (w == VK_SPACE) g_oy += step;
        if (w == VK_CONTROL) g_oy -= step;
        if (w == VK_F11) pvFullScreen(h, -1);   /* second player's screen */
        if (w == VK_OEM_PLUS || w == VK_ADD)
            { g_pvZoom += 10; if (g_pvZoom > 400) g_pvZoom = 400; }
        if (w == VK_OEM_MINUS || w == VK_SUBTRACT)
            { g_pvZoom -= 10; if (g_pvZoom < 50) g_pvZoom = 50; }
        return 0;
    }
    case WM_CLOSE:
        ShowWindow(h, SW_HIDE);
        return 0;
    }
    return DefWindowProcA(h, m, w, l);
}

static BOOL initD3D(void)
{
    WNDCLASSA wc;
    DXGI_SWAP_CHAIN_DESC sd;
    D3D_FEATURE_LEVEL got;
    ID3DBlob *vsb = NULL, *psb = NULL, *err = NULL;
    D3D11_INPUT_ELEMENT_DESC ie[4];
    D3D11_BUFFER_DESC bd;
    D3D11_RASTERIZER_DESC rd;
    D3D11_DEPTH_STENCIL_DESC dsd;
    RECT r;

    ZeroMemory(&wc, sizeof(wc));
    wc.lpfnWndProc = wndProc;
    wc.hInstance = g_self;
    wc.hCursor = LoadCursorA(NULL, (LPCSTR)IDC_ARROW);
    wc.lpszClassName = "VC2View";
    RegisterClassA(&wc);

    r.left = 0; r.top = 0; r.right = g_winW; r.bottom = g_winH;
    AdjustWindowRect(&r, WS_OVERLAPPEDWINDOW, FALSE);
    g_hwnd = CreateWindowExA(WS_EX_NOACTIVATE, "VC2View", "Virtua Cop 2 - 3D preview",
                             WS_OVERLAPPEDWINDOW, CW_USEDEFAULT, CW_USEDEFAULT,
                             r.right - r.left, r.bottom - r.top,
                             NULL, NULL, g_self, NULL);
    if (!g_hwnd) return FALSE;
    if (g_pvFull) pvFullScreen(g_hwnd, 1);
    ShowWindow(g_hwnd, SW_SHOWNOACTIVATE);   /* never take the foreground */

    ZeroMemory(&sd, sizeof(sd));
    sd.BufferCount = 2;
    sd.BufferDesc.Width = g_winW;
    sd.BufferDesc.Height = g_winH;
    sd.BufferDesc.Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    sd.BufferUsage = DXGI_USAGE_RENDER_TARGET_OUTPUT;
    sd.OutputWindow = g_hwnd;
    sd.SampleDesc.Count = 1;
    sd.Windowed = TRUE;
    sd.SwapEffect = DXGI_SWAP_EFFECT_DISCARD;

    if (FAILED(D3D11CreateDeviceAndSwapChain(NULL, D3D_DRIVER_TYPE_HARDWARE, NULL,
              0, NULL, 0, D3D11_SDK_VERSION, &sd, &g_swap, &g_dev, &got, &g_ctx)))
        return FALSE;
    if (!makeTargets()) return FALSE;

    if (FAILED(D3DCompile(SHADER_SRC, lstrlenA(SHADER_SRC), NULL, NULL, NULL,
                          "vs", "vs_4_0", 0, 0, &vsb, &err))) return FALSE;
    if (FAILED(D3DCompile(SHADER_SRC, lstrlenA(SHADER_SRC), NULL, NULL, NULL,
                          "ps", "ps_4_0", 0, 0, &psb, &err))) return FALSE;
    ID3D11Device_CreateVertexShader(g_dev, ID3D10Blob_GetBufferPointer(vsb),
                                    ID3D10Blob_GetBufferSize(vsb), NULL, &g_vs);
    ID3D11Device_CreatePixelShader(g_dev, ID3D10Blob_GetBufferPointer(psb),
                                   ID3D10Blob_GetBufferSize(psb), NULL, &g_ps);

    ZeroMemory(ie, sizeof(ie));
    ie[0].SemanticName = "POSITION";
    ie[0].Format = DXGI_FORMAT_R32G32B32_FLOAT;
    ie[1].SemanticName = "COLOR";
    ie[1].Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    ie[1].AlignedByteOffset = 12;
    ie[2].SemanticName = "TEXCOORD";
    ie[2].Format = DXGI_FORMAT_R32G32_FLOAT;
    ie[2].AlignedByteOffset = 16;
    ie[3].SemanticName = "TEXCOORD";
    ie[3].SemanticIndex = 1;
    ie[3].Format = DXGI_FORMAT_R32_FLOAT;
    ie[3].AlignedByteOffset = 24;
    ID3D11Device_CreateInputLayout(g_dev, ie, 4, ID3D10Blob_GetBufferPointer(vsb),
                                   ID3D10Blob_GetBufferSize(vsb), &g_il);
    ID3D10Blob_Release(vsb); ID3D10Blob_Release(psb);

    ZeroMemory(&bd, sizeof(bd));
    bd.ByteWidth = sizeof(g_draw);
    bd.Usage = D3D11_USAGE_DYNAMIC;
    bd.BindFlags = D3D11_BIND_VERTEX_BUFFER;
    bd.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
    if (FAILED(ID3D11Device_CreateBuffer(g_dev, &bd, NULL, &g_vb))) return FALSE;

    ZeroMemory(&bd, sizeof(bd));
    bd.ByteWidth = 64;
    bd.Usage = D3D11_USAGE_DYNAMIC;
    bd.BindFlags = D3D11_BIND_CONSTANT_BUFFER;
    bd.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
    if (FAILED(ID3D11Device_CreateBuffer(g_dev, &bd, NULL, &g_cb))) return FALSE;

    ZeroMemory(&rd, sizeof(rd));
    rd.FillMode = D3D11_FILL_SOLID;
    rd.CullMode = D3D11_CULL_NONE;      /* winding is unknown, so draw both sides */
    ID3D11Device_CreateRasterizerState(g_dev, &rd, &g_rsSolid);
    rd.FillMode = D3D11_FILL_WIREFRAME;
    ID3D11Device_CreateRasterizerState(g_dev, &rd, &g_rsWire);

    ZeroMemory(&dsd, sizeof(dsd));
    dsd.DepthEnable = g_depthTest ? TRUE : FALSE;
    dsd.DepthWriteMask = g_depthTest ? D3D11_DEPTH_WRITE_MASK_ALL
                                     : D3D11_DEPTH_WRITE_MASK_ZERO;
    dsd.DepthFunc = D3D11_COMPARISON_GREATER;
    ID3D11Device_CreateDepthStencilState(g_dev, &dsd, &g_dss);
    dsd.DepthEnable = FALSE;
    dsd.DepthWriteMask = D3D11_DEPTH_WRITE_MASK_ZERO;
    ID3D11Device_CreateDepthStencilState(g_dev, &dsd, &g_pvDssNo);

    if (g_doTex) {
        D3D11_TEXTURE2D_DESC td;
        D3D11_SAMPLER_DESC sd2;
        ZeroMemory(&td, sizeof(td));
        td.Width = VC2_ATLAS_W; td.Height = VC2_ATLAS_H;
        td.MipLevels = 1; td.ArraySize = 1;
        td.Format = DXGI_FORMAT_B8G8R8A8_UNORM;
        td.SampleDesc.Count = 1;
        td.Usage = D3D11_USAGE_DYNAMIC;
        td.BindFlags = D3D11_BIND_SHADER_RESOURCE;
        td.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
        if (SUCCEEDED(ID3D11Device_CreateTexture2D(g_dev, &td, NULL, &g_pvAtlTex)))
            ID3D11Device_CreateShaderResourceView(g_dev,
                (ID3D11Resource *)g_pvAtlTex, NULL, &g_pvAtlSRV);
        ZeroMemory(&sd2, sizeof(sd2));
        sd2.Filter = D3D11_FILTER_MIN_MAG_MIP_LINEAR;
        sd2.AddressU = sd2.AddressV = sd2.AddressW = D3D11_TEXTURE_ADDRESS_CLAMP;
        ID3D11Device_CreateSamplerState(g_dev, &sd2, &g_pvSamp);
        InterlockedExchange(&g_pvAtlDirty, 1);   /* atlas may already be filled */
    }
    {
        D3D11_BLEND_DESC bld;
        ZeroMemory(&bld, sizeof(bld));
        bld.RenderTarget[0].BlendEnable = TRUE;
        bld.RenderTarget[0].SrcBlend = D3D11_BLEND_ONE;
        bld.RenderTarget[0].DestBlend = D3D11_BLEND_ONE;
        bld.RenderTarget[0].BlendOp = D3D11_BLEND_OP_ADD;
        bld.RenderTarget[0].SrcBlendAlpha = D3D11_BLEND_ONE;
        bld.RenderTarget[0].DestBlendAlpha = D3D11_BLEND_ONE;
        bld.RenderTarget[0].BlendOpAlpha = D3D11_BLEND_OP_ADD;
        bld.RenderTarget[0].RenderTargetWriteMask = D3D11_COLOR_WRITE_ENABLE_ALL;
        ID3D11Device_CreateBlendState(g_dev, &bld, &g_pvBlendAdd);
    }
    return TRUE;
}

static void renderFrame(void)
{
    float clear[4] = { 0.03f, 0.03f, 0.05f, 1.0f };
    D3D11_MAPPED_SUBRESOURCE map;
    D3D11_VIEWPORT vp;
    float mvp[16];
    UINT stride = sizeof(Vtx), offset = 0, count;

    EnterCriticalSection(&g_lock);
    count = g_drawCount;
    g_lastQuads = count;
    {
        UINT i, t = 0;
        for (i = 0; i < count; i += 6) if (g_draw[i].u >= 0.0f) t++;
        g_lastTexQuads = t;
    }
    if (count) {
        if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_vb, 0,
                      D3D11_MAP_WRITE_DISCARD, 0, &map))) {
            CopyMemory(map.pData, g_draw, count * sizeof(Vtx));
            ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_vb, 0);
        }
    }
    if (g_pvAtlTex && g_atlas && InterlockedExchange(&g_pvAtlDirty, 0)) {
        if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_pvAtlTex,
                      0, D3D11_MAP_WRITE_DISCARD, 0, &map))) {
            UINT y;
            for (y = 0; y < VC2_ATLAS_H; y++)
                CopyMemory((BYTE *)map.pData + y * map.RowPitch,
                           g_atlas + (SIZE_T)y * VC2_ATLAS_W, VC2_ATLAS_W * 4);
            ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_pvAtlTex, 0);
        }
    }
    LeaveCriticalSection(&g_lock);

    ID3D11DeviceContext_ClearRenderTargetView(g_ctx, g_rtv, clear);
    ID3D11DeviceContext_ClearDepthStencilView(g_ctx, g_dsv, D3D11_CLEAR_DEPTH, 0.0f, 0);
    ID3D11DeviceContext_OMSetRenderTargets(g_ctx, 1, &g_rtv, g_dsv);
    ID3D11DeviceContext_OMSetDepthStencilState(g_ctx, g_dss, 0);

    ZeroMemory(&vp, sizeof(vp));
    vp.Width = (float)g_winW; vp.Height = (float)g_winH; vp.MaxDepth = 1.0f;
    ID3D11DeviceContext_RSSetViewports(g_ctx, 1, &vp);
    ID3D11DeviceContext_RSSetState(g_ctx, g_wire ? g_rsWire : g_rsSolid);

    if (g_showAtlas && g_pvAtlSRV) {
        /* identity mvp, NDC quad, neutral colour: the raw sheet, 1:1 light */
        static const Vtx av[6] = {
            { -1,  1, 0.5f, 0xFF404040u, 0, 0 },
            {  1,  1, 0.5f, 0xFF404040u, 1, 0 },
            {  1, -1, 0.5f, 0xFF404040u, 1, 1 },
            { -1,  1, 0.5f, 0xFF404040u, 0, 0 },
            {  1, -1, 0.5f, 0xFF404040u, 1, 1 },
            { -1, -1, 0.5f, 0xFF404040u, 0, 1 },
        };
        matIdent(mvp);
        if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_vb, 0,
                      D3D11_MAP_WRITE_DISCARD, 0, &map))) {
            CopyMemory(map.pData, av, sizeof(av));
            ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_vb, 0);
        }
        count = 6;
    } else
    buildMVP(mvp);
    if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_cb, 0,
                  D3D11_MAP_WRITE_DISCARD, 0, &map))) {
        CopyMemory(map.pData, mvp, sizeof(mvp));
        ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_cb, 0);
    }

    ID3D11DeviceContext_IASetInputLayout(g_ctx, g_il);
    ID3D11DeviceContext_IASetPrimitiveTopology(g_ctx,
        D3D11_PRIMITIVE_TOPOLOGY_TRIANGLELIST);
    ID3D11DeviceContext_IASetVertexBuffers(g_ctx, 0, 1, &g_vb, &stride, &offset);
    ID3D11DeviceContext_VSSetShader(g_ctx, g_vs, NULL, 0);
    ID3D11DeviceContext_VSSetConstantBuffers(g_ctx, 0, 1, &g_cb);
    ID3D11DeviceContext_PSSetShader(g_ctx, g_ps, NULL, 0);
    if (g_pvAtlSRV) {
        ID3D11DeviceContext_PSSetShaderResources(g_ctx, 0, 1, &g_pvAtlSRV);
        ID3D11DeviceContext_PSSetSamplers(g_ctx, 0, 1, &g_pvSamp);
    }
    {
        float bf[4] = { 0, 0, 0, 0 };
        ID3D11DeviceContext_OMSetBlendState(g_ctx, NULL, bf, 0xFFFFFFFF);
        ID3D11DeviceContext_OMSetDepthStencilState(g_ctx,
            g_showAtlas ? g_pvDssNo : g_dss, 0);
        if (count) ID3D11DeviceContext_Draw(g_ctx, count, 0);
    }

    IDXGISwapChain_Present(g_swap, 1, 0);
}

static DWORD WINAPI viewThread(LPVOID p)
{
    MSG msg;
    (void)p;
    if (!initD3D()) return 0;
    g_ready = TRUE;
    for (;;) {
        while (PeekMessageA(&msg, NULL, 0, 0, PM_REMOVE)) {
            TranslateMessage(&msg);
            DispatchMessageA(&msg);
        }
        renderFrame();
        {
            static DWORD last;
            DWORD now = GetTickCount();
            if (now - last > 300) {
                char t[256];
                last = now;
                {
                    char sl[128]; int i, n = 0;
                    sl[0] = 0;
                    for (i = 0; i < MAX_SLOTS && n < 4; i++) {
                        if (i == SLOT_INIT || i == SLOT_QUAD || i == SLOT_TEX ||
                            i == SLOT_FLUSH || i == SLOT_GETINFO) continue;
                        if (g_slotShown[i] > 0) {
                            char one[32];
                            wsprintfA(one, " s%d:%d", i, (int)g_slotShown[i]);
                            lstrcatA(sl, one);
                            n++;
                        }
                    }
                    wsprintfA(t, "VC2 v10.0 %s%s C%d - TEX %u/%u reg %d - amb %d/%d/%d - SPR %d/%d/%d/%d"
                              " - WC %d/%d/%d %d%%%s - sx %d..%d sy %d..%d - hit %u..%u miss %u..%u -%s"
                              " - fov%d - g%d%%[G] uv%d[T] a%d[K] %s%s[U][A][P]",
                              g_cullState == 1 ? "NOCULL" :
                              g_cullState == 2 ? "cull?" :
                              g_cullState == 3 ? "cull!" : "cull:on",
                              g_ocullState == 1 ? "+OBJ" :
                              g_ocullState == 2 ? "+obj?" :
                              g_ocullState == 3 ? "+obj!" : "",
                              g_cityState == 1 ? g_cityShown :
                              g_cityState == 2 ? -1 : g_cityState == 3 ? -2 : 0,
                              g_lastTexQuads, g_lastQuads / 6, g_regCount,
                              g_amb[0], g_amb[1], g_amb[2],
                              (int)g_sprShown[0], (int)g_sprShown[1],
                              (int)g_sprShown[2], (int)g_sprShown[3],
                              g_wcDrawn, g_wcLive, g_wcN, g_wcMatchRate,
                              g_wcOn ? (g_wcTrack ? "" : " lost") : " off",
                              (int)g_sxMinS, (int)g_sxMaxS,
                              (int)g_syMinS, (int)g_syMaxS,
                              g_idHitMinS == ~0u ? 0 : g_idHitMinS, g_idHitMaxS,
                              g_idMissMinS == ~0u ? 0 : g_idMissMinS, g_idMissMaxS,
                              sl[0] ? sl : " s:-",
                              g_projOk ? (int)(g_projFov + 0.5f) : 0,
                              (int)g_texGain, (int)g_uvOrder,
                              (int)g_alphaMode,
                              g_neutral ? "NEU " : "",
                              g_showAtlas ? "ATL " :
                              g_skip3 == 0 ? "L3:on " :
                              g_skip3 == 1 ? "L3:off " : "");
                }
                SetWindowTextA(g_hwnd, t);
            }
        }
    }
}

/* ------------------------------------------------------------- slot wrappers */

/* Who decides that a model exists this frame? The chain runs
 *   ??? -> PPJ2DD 0x004421F0 -> 0x00442430 -> 0x00442560 -> the quad slot,
 * and the top of it is not in the exe: the stage libraries PG_STG1/2/3.DLL
 * get exe function pointers through GetPGDLLInfo and call them INDIRECTLY.
 * The first version of this probe looked for a direct call opcode in front of
 * every return address on the stack, which by that very fact could never
 * match - and it walked 16 kB of stack per quad through IsBadReadPtr, which
 * is what made the window take seconds to come back.
 * This one reads the whole call stack instead: bounds fetched once, every
 * plausible return address kept, whatever call form produced it. */
static DWORD g_objFrom[24];
static DWORD g_objFromBase[24];
static BYTE  g_objFromKind[24];
static int   g_objFromN;
static int   g_objScans;
static DWORD g_objDirect;       /* return address of whoever wanted the model */
static DWORD g_objDirectObj;    /* and the model pointer it handed over       */

static int retKind(const BYTE *p)
{
    /* p is the return address: what stands directly in front of it.
     * p may point at the very first bytes of a module, in which case p[-7]
     * lands in an unmapped page - this check is why v8.7 crashed on [P]. */
    if (!p || IsBadReadPtr(p - 8, 8)) return 0;
    if (p[-5] == 0xE8) return 1;                          /* call rel32     */
    if (p[-2] == 0xFF && (p[-1] & 0xF8) == 0xD0) return 2; /* call reg      */
    if (p[-3] == 0xFF && (p[-2] & 0xF8) == 0x50) return 3; /* call [reg+i8] */
    if (p[-6] == 0xFF && (p[-5] & 0xF8) == 0x90) return 4; /* call [reg+i32]*/
    if (p[-6] == 0xFF && p[-5] == 0x15) return 5;          /* call [abs]    */
    if (p[-7] == 0xFF && (p[-6] & 0x38) == 0x10) return 6; /* call [sib+i32]*/
    return 0;
}

/* module ranges, so a stack walk does not pay for a VirtualQuery per dword */
typedef struct { DWORD lo, hi; char name[32]; } ModRange;
static ModRange g_mods[48];
static int      g_modsN;

static const ModRange *modOf(DWORD v)
{
    int i;
    MEMORY_BASIC_INFORMATION mb;
    for (i = 0; i < g_modsN; i++)
        if (v >= g_mods[i].lo && v < g_mods[i].hi)
            return g_mods[i].name[0] ? &g_mods[i] : NULL;
    if (g_modsN >= 48) return NULL;
    if (!VirtualQuery((void *)(DWORD_PTR)v, &mb, sizeof(mb))) return NULL;
    g_mods[g_modsN].lo = (DWORD)(DWORD_PTR)mb.BaseAddress;
    g_mods[g_modsN].hi = g_mods[g_modsN].lo + (DWORD)mb.RegionSize;
    g_mods[g_modsN].name[0] = 0;
    if (mb.State == MEM_COMMIT && mb.Type == MEM_IMAGE &&
        (mb.Protect & (PAGE_EXECUTE | PAGE_EXECUTE_READ |
                       PAGE_EXECUTE_READWRITE | PAGE_EXECUTE_WRITECOPY))) {
        char path[MAX_PATH];
        int c, sl = 0, n;
        path[0] = 0;
        GetModuleFileNameA((HMODULE)mb.AllocationBase, path, MAX_PATH);
        for (c = 0; path[c]; c++) if (path[c] == 92) sl = c + 1;
        for (n = 0; n < 31 && path[sl + n]; n++)
            g_mods[g_modsN].name[n] = path[sl + n];
        g_mods[g_modsN].name[n] = 0;
        if (!n) g_mods[g_modsN].name[0] = 0;
        g_mods[g_modsN].lo = (DWORD)(DWORD_PTR)mb.AllocationBase;
    }
    g_modsN++;
    return g_mods[g_modsN - 1].name[0] ? &g_mods[g_modsN - 1] : NULL;
}

/* The caller cannot be found by scanning: between our frame and it lie the
 * 0x36B0 bytes of uninitialised locals that 0x004421F0 keeps for a model's
 * transformed vertices, and they are full of leftovers from earlier, deeper
 * calls into the display driver - which is exactly what filled the previous
 * two dumps. So compute the slot instead of hunting for it.
 *
 *   0x004421F0 entry:      esp -> its own return address, call it R
 *   after the stack probe: esp = R - 0x36B0
 *   push esi:              esp = R - 0x36B4
 *   push ecx, edx, esi:    esp = R - 0x36C0      (args of 0x00442560)
 *   call 0x00442560:       esp = R - 0x36C4      <- holds 0x00442263
 *
 * so having found 0x00442263 on the stack at S, the address of whoever asked
 * for this model sits at S + 0x36C4, full stop.
 */
static void scanObjectCaller(void *frame)
{
    MEMORY_BASIC_INFORMATION mbi;
    DWORD *sp = (DWORD *)frame, *end;
    BYTE *exe = (BYTE *)GetModuleHandleA(NULL);
    DWORD inner;

    if (g_objScans > 2 || !exe) return;
    g_objScans++;
    inner = (DWORD)(DWORD_PTR)(exe + 0x42263);
    if (!VirtualQuery(frame, &mbi, sizeof(mbi))) return;
    end = (DWORD *)((BYTE *)mbi.BaseAddress + mbi.RegionSize);
    if (end > sp + 0x4000) end = sp + 0x4000;

    /* the slot is not searched for, it is computed: wrap_quad's argument sits
     * at esp+4 of the call at 0x00442935, and from there to the slot holding
     * 0x00442263 is a fixed 0x98 (0x84 locals + four pushes + one argument),
     * after which +0x36C4 more reaches the return address of 0x004421F0. */
    {
        DWORD *s = (DWORD *)((BYTE *)frame + 0x98);
        if (!IsBadReadPtr(s, 4) && *s == inner &&
            !IsBadReadPtr(s + (0x36C4 / 4), 8)) {
            g_objDirect = s[0x36C4 / 4];
            g_objDirectObj = s[0x36C4 / 4 + 1];
        }
    }

    for (; sp < end; sp++) {
        DWORD *up;
        if (*sp != inner) continue;
        up = sp + (0x36C4 / 4);
        if (up >= end) break;
        /* the computed slot first, then the frames above it for context */
        for (; up < end && g_objFromN < 24; up++) {
            DWORD v = *up;
            const ModRange *m;
            int kind, i;
            if (v < 0x400000) continue;
            m = modOf(v);
            if (!m) continue;
            kind = retKind((BYTE *)(DWORD_PTR)v);
            if (!kind) continue;
            for (i = 0; i < g_objFromN; i++) if (g_objFrom[i] == v) break;
            if (i < g_objFromN) continue;
            g_objFrom[g_objFromN] = v;
            g_objFromBase[g_objFromN] = m->lo;
            g_objFromKind[g_objFromN] = (BYTE)kind;
            g_objFromN++;
        }
        break;
    }
}

static DWORD __stdcall wrap_quad(void *cmd)
{
    const DWORD *q = (const DWORD *)cmd;
    readProjection();
    if (g_probeAt) scanObjectCaller(&cmd);
    {   /* the culling lives just above whoever calls us, and nothing in the
         * import tables says who that is - so ask the stack. */
        DWORD ra = (DWORD)(DWORD_PTR)__builtin_return_address(0);
        int i;
        g_quadRa = ra;
        for (i = 0; i < g_quadFromN; i++) if (g_quadFrom[i] == ra) break;
        if (i == g_quadFromN && g_quadFromN < 8) {
            g_quadFrom[g_quadFromN++] = ra;
            patchCullFromRet(ra);
        }
    }
    {   /* which transform produced this quad */
        BYTE *base = (BYTE *)GetModuleHandleA(NULL);
        const float **pp = (const float **)(base + MTX_PTR_RVA);
        const float *m;
        if (base && !IsBadReadPtr(pp, 4) && (m = *pp) != NULL &&
            !IsBadReadPtr(m, 48)) {
            int i, j;
            g_mtxTotal++;
            for (i = 0; i < g_mtxN; i++) {
                for (j = 0; j < 12; j++)
                    if (g_mtx[i].m[j] != m[j]) break;
                if (j == 12) { g_mtx[i].n++; break; }
            }
            if (i == g_mtxN && g_mtxN < 12) {
                for (j = 0; j < 12; j++) g_mtx[g_mtxN].m[j] = m[j];
                g_mtx[g_mtxN].n = 1;
                g_mtxN++;
            }
        }
    }
    if (!g_upFrame && !g_pass) {
        /* CAMERA HOOK TIME IS TOO EARLY. Reading the matrix straight after
         * the game's camera call gave a pointer to numbers that are not a
         * rotation at all (up ok 0 in the log, every frame), so levelworld
         * and skylock were both sitting inert. Here the engine has just
         * transformed a vertex through that very matrix and handed us the
         * quad, so it is live by definition. */
        g_upFrame = 1;
        captureUp((BYTE *)GetModuleHandleA(NULL));
    }
    if (g_inClip && g_trueClip) {
        /* a piece of a polygon the clipper detour holds: the flat window
         * gets it below, VR gets the whole polygon from clipThunk instead */
        if (!g_clipRecOk && !IsBadReadPtr(cmd, sizeof(g_clipRec))) {
            CopyMemory(g_clipRec, cmd, sizeof(g_clipRec));
            g_clipRecOk = 1;
        }
        g_clipEmit++;
        g_clipHeld++;
    } else if ((g_ready || g_doShare) && !IsBadReadPtr(cmd, 0x58)) {
        EnterCriticalSection(&g_lock);
        pushQuad((const DWORD *)cmd);
        LeaveCriticalSection(&g_lock);
    }
    if (g_pass) return 1;              /* a cube pass: ours alone, never HGL_D3D's */
    /* ------------------------------------------------------- the 3000 wall
     * HGL_D3D builds the frame in a flat list: 0x10005FD0 sets the write
     * pointer 0x10C1C534 to 0x10C1D650 and every quad advances it by 0xCC
     * bytes (0x100056A5) with NO bound check anywhere. The next thing in the
     * DLL image is the per-slot texture table at 0x10CB2D20, which is
     * 0x956D0 bytes further on - exactly 3000 quads.
     *
     * So quad 3001 does not overflow into spare memory, it writes straight
     * over the texture table: first the textures go wrong, then the pointers
     * in it are garbage and the game dies. That is the whole story behind
     * "cityahead above 2 crashes" and "the pavement textures went mad".
     *
     * Our own buffer holds 40000, so past the wall we keep the quad and stop
     * handing it to HGL_D3D. The game's own window loses the far geometry;
     * the VR view does not. */
    g_quadSent++;
    if (g_quadCap > 0 && g_quadSent > g_quadCap) { g_quadHeld++; return 1; }
    /* A quad the near plane deleted only exists because we NOPed the four
     * rejects in 0x00442560. Its w are zero and HGL_D3D computes sz = K / w,
     * so handing it over is a divide by zero and a frame of garbage. It is
     * ours alone; the game's own window is exactly what it was. */
    if (g_behindOn && g_trueXyz &&
        (q[6] == 0 || q[10] == 0 || q[14] == 0 || q[18] == 0)) {
        g_behindHeld++;
        return 1;
    }
    return ((DWORD (__stdcall *)(void *))g_real[SLOT_QUAD])(cmd);
}

/* HGL_D3D 0x10005C80: three signed offsets added to every quad shade, with a
 * (0x50,0,0) special case that means "no light". Without them everything came
 * out too dark and had to be faked with texgain. */
static DWORD __stdcall wrap_light(void *cmd)
{
    if (!IsBadReadPtr(cmd, 16)) {
        const DWORD *c = (const DWORD *)cmd;
        if (c[0] == 0x50 && c[1] == 0 && c[2] == 0) {
            g_amb[0] = g_amb[1] = g_amb[2] = 0;
        } else {
            g_amb[0] = (int)c[0];
            g_amb[1] = (int)c[1];
            g_amb[2] = (int)c[2];
        }
    }
    return ((DWORD (__stdcall *)(void *))g_real[SLOT_LIGHT])(cmd);
}

/* screen sprites: rect + texture + shade + priority 0..3 at +0x18. The sky and
 * the HUD live here. Counted only for now, drawing comes next version. */
static DWORD __stdcall wrap_sprite(void *cmd)
{
    if (g_pass) return 1;              /* screen-space blit from a rotated pass */
    if (!IsBadReadPtr(cmd, 0x60)) {
        const DWORD *s = (const DWORD *)cmd;
        int p = (int)s[6];
        if (p < 0) p = 0;
        if (p > 3) p = 3;
        InterlockedIncrement(&g_sprN[p]);
        if (g_ready || g_doShare) {
            EnterCriticalSection(&g_lock);
            pushSprite(s);
            LeaveCriticalSection(&g_lock);
        }
    }
    return ((DWORD (__stdcall *)(void *))g_real[SLOT_SPRITE])(cmd);
}

static void publish(const Vtx *v, UINT n)
{
    UINT i;
    if (!g_share) return;
    if (n > VC2_MAX_VERTS) n = VC2_MAX_VERTS;

    g_share->seq++;                     /* odd: writing */
    _ReadWriteBarrier();
    g_share->magic = VC2_SHARE_MAGIC;
    g_share->version = VC2_SHARE_VERSION;
    g_share->frame++;
    g_share->vertex_count = n;
    /* publish the LIVE zoomed fov, not the static ini one. the game walks
     * its focal length during zoom (word 0x004DB8A4); g_projFov tracks it
     * (see readProjection). vc2vr rebuilds g_gfx from this each frame, so
     * the aim reprojection must get the fov the game is projecting through
     * RIGHT NOW - otherwise the crosshair drifts from the laser exactly
     * while zoomed. fall back to the ini fov until the live read is valid. */
    g_share->fov_degrees = g_fovDeg;
    g_share->units_per_metre = g_unitsPerMetre;
    g_share->reserved[0] = n;      /* no translucent tail, ever */
    g_share->reserved[1] = (g_drawL3End < n) ? g_drawL3End : n;
    /* +1 so that 0 keeps meaning "an older DLL that never said" */
    g_share->reserved[2] = (g_ovStart <= n) ? g_ovStart + 1u : 0u;
    for (i = 0; i < n; i++) {
        g_share->verts[i].x = v[i].x;
        g_share->verts[i].y = v[i].y;
        g_share->verts[i].z = v[i].z;
        g_share->verts[i].colour = v[i].col;
        g_share->verts[i].u = v[i].u;
        g_share->verts[i].v = v[i].v;
        g_share->verts[i].depth = v[i].d;
    }
    _ReadWriteBarrier();
    g_share->seq++;                     /* even: settled */
}

/* --------------------------------------------------------------- our own HUD
 * The game's drum is a 72x72 texture and the life icon is 28x43. On a monitor
 * that is a HUD; through a lens two inches from the eye it is twenty pixels of
 * mush, and no filter can put back detail that was never drawn. Stretching it
 * only makes the mush bigger.
 *
 * So draw it instead. The state is already known - see the id decoding in
 * pushSprite - and the shapes are a cylinder with six chambers and a row of
 * pips, which is to say circles. Circles made of triangles have no resolution
 * at all: they are exactly as sharp as the headset can show, at any size, at
 * any distance, in any lens. The vertices carry u = -1, the shader's "no
 * texture, take the colour as it is", so nothing is sampled and nothing is
 * blurred.
 *
 * Two things decide whether that reads as an object or as a cartoon:
 *
 * - Shading. A flat fill is a sticker. Every ring here walks its colour from
 *   dark to bright along one light direction (up and to the left), which for a
 *   ring of quads costs nothing: the colour is per quad, and a ring is quads.
 *   That alone turns a grey circle into a steel one.
 * - Proportion. Six fat discs on a black field at two thirds of the radius is
 *   a daisy. A cylinder is a wide steel rim, a recessed dark face, six small
 *   case heads well clear of each other, and a hub in the middle - the hub in
 *   particular is what stops the eye reading flower petals.
 *
 * Laid out in the game's own 640x480 overlay coordinates, on purpose: that
 * puts our drum exactly where the game's drum was, so hudspread, hudscale and
 * sprdist keep working on it unchanged and the whole overlay still moves as
 * one piece.
 *
 * One correction the game's own sprites do not get: the overlay grid is not
 * isotropic in angle. A pixel is 1/fx of a radian across and 1/fy down, and
 * fy = 1.125 fx, so anything drawn round in overlay pixels arrives in the
 * headset 12 percent squat. The game never cared - its sprites are art, and
 * art that is 12 percent squat is just art. Circles that are meant to be
 * circles do care, so every y radius below is multiplied by fy/fx.
 */
#define HUD_A 0x40000000u                 /* alpha the cutout shader lets past */
#define HUDC(r,g,b) (HUD_A | ((DWORD)(b) << 16) | ((DWORD)(g) << 8) | (DWORD)(r))

static float g_hudAsp = 1.125f;           /* fy/fx, set once per frame         */

static DWORD hudMix(DWORD a, DWORD b, float t)
{
    int i; DWORD o = HUD_A;
    if (t < 0.0f) t = 0.0f;
    if (t > 1.0f) t = 1.0f;
    for (i = 0; i < 3; i++) {
        int ca = (int)((a >> (i * 8)) & 0xFF), cb = (int)((b >> (i * 8)) & 0xFF);
        int c  = ca + (int)((float)(cb - ca) * t + 0.5f);
        o |= (DWORD)(c & 0xFF) << (i * 8);
    }
    return o;
}

static void hudVtx(float px, float py, float dist, DWORD col)
{
    Vtx *v;
    if (g_buildCount >= MAX_QUADS * 6) return;
    v = &g_build[g_buildCount];
    v->x =  (px - g_cx) * dist / g_fxIni;
    v->y = -(py - g_cy) * dist / g_fyIni;
    v->z = -dist;
    v->col = col;
    v->u = -1.0f;
    v->v = -1.0f;
    v->d = 1.0f;                          /* overlay depth, as the sprites use */
    g_buildCount++;
}

/* one flat quad, given in overlay coordinates; key 0 = painted last, in front.
 * equal keys keep submission order in the sort, so these layer back to front
 * in the order they are written below */
static void hudQuad(const float *a, const float *b, const float *c,
                    const float *d, float dist, DWORD col)
{
    if (g_buildCount + 6 > MAX_QUADS * 6) return;
    g_quadKey[g_buildCount / 6] = 0;
    g_quadFlat[g_buildCount / 6] = 1;
    hudVtx(a[0], a[1], dist, col);
    hudVtx(b[0], b[1], dist, col);
    hudVtx(c[0], c[1], dist, col);
    hudVtx(a[0], a[1], dist, col);
    hudVtx(c[0], c[1], dist, col);
    hudVtx(d[0], d[1], dist, col);
}

/* a flat disc as a fan of quads - two segments per quad */
static void hudDisc(float cx, float cy, float r, float dist, DWORD col, int segs)
{
    int i;
    float ry = r * g_hudAsp;
    if (segs < 4) segs = 4;
    segs &= ~1;
    for (i = 0; i < segs; i += 2) {
        float a0 = (float)i * 6.2831853f / (float)segs;
        float a1 = (float)(i + 1) * 6.2831853f / (float)segs;
        float a2 = (float)(i + 2) * 6.2831853f / (float)segs;
        float p0[2], p1[2], p2[2], pc[2];
        pc[0] = cx; pc[1] = cy;
        p0[0] = cx + r * (float)cos(a0); p0[1] = cy + ry * (float)sin(a0);
        p1[0] = cx + r * (float)cos(a1); p1[1] = cy + ry * (float)sin(a1);
        p2[0] = cx + r * (float)cos(a2); p2[1] = cy + ry * (float)sin(a2);
        hudQuad(pc, p0, p1, p2, dist, col);
    }
}

/* a shaded ring: one quad per segment, its colour taken from how much that
 * segment faces the light. This is the whole of the lighting model and it is
 * the difference between a steel cylinder and a grey circle. */
static void hudRing(float cx, float cy, float r0, float r1, float dist,
                    DWORD dark, DWORD bright, int segs)
{
    int i;
    if (segs < 6) segs = 6;
    for (i = 0; i < segs; i++) {
        float a0 = (float)i * 6.2831853f / (float)segs;
        float a1 = (float)(i + 1) * 6.2831853f / (float)segs;
        float am = (a0 + a1) * 0.5f;
        /* light from up and to the left; overlay y grows downwards */
        float t = (-0.7071f * (float)cos(am) - 0.7071f * (float)sin(am) + 1.0f)
                  * 0.5f;
        DWORD col = hudMix(dark, bright, t);
        float p[4][2];
        p[0][0] = cx + r0 * (float)cos(a0);
        p[0][1] = cy + r0 * g_hudAsp * (float)sin(a0);
        p[1][0] = cx + r1 * (float)cos(a0);
        p[1][1] = cy + r1 * g_hudAsp * (float)sin(a0);
        p[2][0] = cx + r1 * (float)cos(a1);
        p[2][1] = cy + r1 * g_hudAsp * (float)sin(a1);
        p[3][0] = cx + r0 * (float)cos(a1);
        p[3][1] = cy + r0 * g_hudAsp * (float)sin(a1);
        hudQuad(p[0], p[1], p[2], p[3], dist, col);
    }
}

/* a closed outline as a fan from its centre; points are in units of sx, sy */
static void hudPoly(float cx, float cy, const float *pts, int n,
                    float sx, float sy, float dist, DWORD top, DWORD bot)
{
    int i;
    for (i = 0; i < n; i += 2) {
        int i0 = i, i1 = (i + 1) % n, i2 = (i + 2) % n;
        float pc[2], p0[2], p1[2], p2[2];
        DWORD col = hudMix(top, bot, (pts[i1 * 2 + 1] + 1.0f) * 0.5f);
        pc[0] = cx; pc[1] = cy;
        p0[0] = cx + pts[i0 * 2] * sx; p0[1] = cy + pts[i0 * 2 + 1] * sy;
        p1[0] = cx + pts[i1 * 2] * sx; p1[1] = cy + pts[i1 * 2 + 1] * sy;
        p2[0] = cx + pts[i2 * 2] * sx; p2[1] = cy + pts[i2 * 2 + 1] * sy;
        hudQuad(pc, p0, p1, p2, dist, col);
    }
}

/* a revolver cylinder from behind: steel rim, recessed face, six case heads,
 * centre hub. Radii are in overlay pixels, so the whole thing lands in the
 * 72x72 the game's own drum sprite occupied. */
static void hudDrum(float ox, float oy, int rounds, float s, float dist)
{
    const DWORD OUTL    = HUDC(0x05, 0x05, 0x06);
    const DWORD STEEL_D = HUDC(0x28, 0x28, 0x2A);
    const DWORD STEEL_B = HUDC(0xD2, 0xD4, 0xD8);
    const DWORD FACE_D  = HUDC(0x14, 0x14, 0x16);
    const DWORD FACE_B  = HUDC(0x3A, 0x3C, 0x40);
    const DWORD BRASS_D = HUDC(0x6E, 0x52, 0x1E);
    const DWORD BRASS_B = HUDC(0xF2, 0xDC, 0xA2);
    const DWORD PRIM_D  = HUDC(0x5A, 0x46, 0x22);
    const DWORD PRIM_B  = HUDC(0xC8, 0xAE, 0x76);
    const DWORD HOLE    = HUDC(0x07, 0x07, 0x08);
    const DWORD MOUTH_D = HUDC(0x10, 0x10, 0x11);
    const DWORD MOUTH_B = HUDC(0x50, 0x52, 0x56);
    int i;

    hudDisc(ox, oy, 36.0f * s, dist, OUTL, 32);
    hudRing(ox, oy, 28.0f * s, 35.0f * s, dist, STEEL_D, STEEL_B, 32);
    hudRing(ox, oy, 26.5f * s, 28.0f * s, dist, STEEL_B, STEEL_D, 24);
    hudDisc(ox, oy, 26.8f * s, dist, FACE_D, 20);
    hudRing(ox, oy,  8.0f * s, 26.5f * s, dist, FACE_D, FACE_B, 24);

    for (i = 0; i < 6; i++) {
        float a  = (float)i * 1.0471976f - 1.5707963f;   /* one chamber on top */
        float cx = ox + 17.0f * s * (float)cos(a);
        float cy = oy + 17.0f * s * g_hudAsp * (float)sin(a);
        hudDisc(cx, cy, 7.0f * s, dist, HOLE, 12);
        if (i < rounds) {
            hudRing(cx, cy, 3.2f * s, 6.4f * s, dist, BRASS_D, BRASS_B, 12);
            hudDisc(cx, cy, 3.3f * s, dist, PRIM_D, 10);
            hudRing(cx, cy, 1.4f * s, 3.2f * s, dist, PRIM_D, PRIM_B, 10);
        } else {
            hudRing(cx, cy, 5.2f * s, 6.6f * s, dist, MOUTH_D, MOUTH_B, 12);
        }
    }

    hudDisc(ox, oy, 7.2f * s, dist, HUDC(0x0A, 0x0A, 0x0B), 12);
    hudRing(ox, oy, 4.0f * s, 6.6f * s, dist, STEEL_D, STEEL_B, 12);
    hudDisc(ox, oy, 4.2f * s, dist, HUDC(0x1A, 0x1A, 0x1C), 10);
}

/* one life: a shield. A row of plain dots says nothing; a shield says police
 * and survives being small. Points are the outline in unit coordinates. */
static const float HUD_SHIELD[] = {
    -0.92f, -1.00f,  0.00f, -1.00f,  0.92f, -1.00f,  1.00f, -0.72f,
     1.00f, -0.10f,  0.90f,  0.32f,  0.60f,  0.68f,  0.30f,  0.90f,
     0.00f,  1.00f, -0.30f,  0.90f, -0.60f,  0.68f, -0.90f,  0.32f,
    -1.00f, -0.10f, -1.00f, -0.72f
};
#define HUD_SHIELD_N 14

static void hudBadge(float ox, float oy, float s, float dist)
{
    const DWORD OUTL = HUDC(0x05, 0x05, 0x06);
    const DWORD RED_T = HUDC(0xD8, 0x2E, 0x2A);
    const DWORD RED_B = HUDC(0x84, 0x12, 0x18);
    const DWORD GLOSS = HUDC(0xF4, 0x70, 0x58);
    float a = g_hudAsp;
    hudPoly(ox, oy, HUD_SHIELD, HUD_SHIELD_N,
            11.6f * s, 14.6f * s * a, dist, OUTL, OUTL);
    hudPoly(ox, oy, HUD_SHIELD, HUD_SHIELD_N,
            10.0f * s, 12.8f * s * a, dist, RED_T, RED_B);
    hudPoly(ox, oy - 4.6f * s * a, HUD_SHIELD, HUD_SHIELD_N,
            6.6f * s, 5.4f * s * a, dist, GLOSS, GLOSS);
}

static void hudPip(float ox, float oy, float s, float dist)
{
    hudDisc(ox, oy, 9.5f * s, dist, HUDC(0x05, 0x05, 0x06), 16);
    hudDisc(ox, oy, 8.2f * s, dist, HUDC(0xC0, 0x24, 0x22), 16);
    hudDisc(ox - 2.4f * s, oy - 2.6f * s * g_hudAsp, 3.4f * s, dist,
            HUDC(0xF2, 0x76, 0x60), 12);
}

static void hudDrawOwn(void)
{
    /* the drum sits where the game's drum sat: player 1 centred on (50, 356),
     * player 2 mirrored on (588, 356); the life row runs from x = 86 outwards
     * at y = 421, one icon every 29 - all of it the game's own layout, so the
     * overlay keeps moving as one piece under hudspread */
    static const float drumX[2] = { 50.0f, 588.0f };
    static const float lifeX[2] = { 86.0f, 552.0f };
    static const float lifeStep[2] = { 29.0f, -29.0f };
    float dist = g_sprDist;
    float sp = (float)g_hudSpread / 100.0f;
    float sc = (float)g_hudScale / 100.0f * (float)g_hudOwnSize / 100.0f;
    int p, i;

    if (!g_hudOwn || dist <= 1.0f) return;
    g_hudAsp = (g_fxIni > 1.0f) ? g_fyIni / g_fxIni : 1.125f;

    for (p = 0; p < 2; p++) {
        int have = (g_ammoIdS[p] != 0);
        float gx = drumX[p], gy = 356.0f;
        float ox = g_cx + (gx - g_cx) * sp, oy = g_cy + (gy - g_cy) * sp;
        if (have) {
            DWORD base = p ? 1399u : 1378u;
            int rounds = 6 - (int)((g_ammoIdS[p] - base) % 7u);
            if (rounds < 0) rounds = 0;
            if (rounds > 6) rounds = 6;
            hudDrum(ox, oy, rounds, sc, dist);
        }
        if (g_hudLives >= 2) continue;
        for (i = 0; i < g_lifeNS[p] && i < 12; i++) {
            float lx = lifeX[p] + lifeStep[p] * (float)i;
            float ly = 421.0f;
            float px = g_cx + (lx - g_cx) * sp;
            float py = g_cy + (ly - g_cy) * sp;
            if (g_hudLives == 1) hudPip(px, py, sc, dist);
            else                 hudBadge(px, py, sc, dist);
        }
    }
}

static DWORD __stdcall wrap_flush(void *arg)
{
    EnterCriticalSection(&g_lock);
    wcTrackCamera();
    wcEmit();
    g_wcFrame++;
    /* one generation per frame: an entry from the previous frame describes a
     * vertex under the previous camera, and the stack buffers it was keyed on
     * have been reused since */
    g_txGen++;
    if (!g_txGen) g_txGen = 1;
    g_txTag = 0;
    g_txInsS = g_txIns; g_txHitS = g_txHit; g_txMissS = g_txMiss;
    g_txBumpS = g_txBump; g_txFullS = g_txFull;
    g_txBadHitS = g_txBadHit; g_txBadHit = 0;
    g_bentDropS = g_bentDrop; g_bentDrop = 0;
    g_behindQS = g_behindQ;
    g_txIns = g_txHit = g_txMiss = g_behindQ = g_txBump = g_txFull = 0;
    g_exDupS = g_exDup; g_exQuadsS = g_exQuads; g_exFullS = g_exFull; g_exSeenNS = g_exSeenN;
    g_exDup = g_exQuads = g_exFull = g_exSeenN = 0;
    g_clipPolyS = g_clipPoly; g_clipNoRecS = g_clipNoRec; g_clipPiecesS = g_clipPieces;
    g_clipHeldS = g_clipHeld; g_clipDeepS = g_clipDeep; g_clipDupS = g_clipDup;
    g_clipPoly = g_clipNoRec = g_clipPieces = g_clipHeld = g_clipDeep = g_clipDup = 0;
    {   int li;
        {   int li;
        for (li = 0; li < 16; li++) { g_ldS[li] = g_ld[li]; g_ld[li].n = 0;
                                       g_ld0S[li] = g_ld0[li]; g_ld0[li].n = 0; }
        g_bigAreaS = g_bigArea; g_bigDistS = g_bigDist; g_bigTexS = g_bigTex;
        g_bigArea = 0.0f;
        g_wideSrS = g_wideSr; g_wideDistS = g_wideDist;
        g_wideAreaS = g_wideArea; g_wideTexS = g_wideTex;
        g_wideSr = 0.0f;
    }
    g_bigMissS = g_bigMiss; g_bigMiss = 0;
    g_farSprS = g_farSpr; g_farSprTexS = g_farSprTex;
    g_farSprWS = g_farSprW; g_farSprHS = g_farSprH;
    g_farSpr = 0; g_farSprW = g_farSprH = 0.0f;
    g_legacyQS = g_legacyQ; g_legacyQ = 0;
        for (li = 0; li < 16; li++) { g_legacyLS[li] = g_legacyL[li]; g_legacyL[li] = 0; }
    }
    {
        int i;
        for (i = 0; i < 8; i++) {
            g_passSeenS[i] = g_passSeen[i]; g_passKeptS[i] = g_passKept[i];
            g_passSeen[i] = g_passKept[i] = 0;
        }
        g_passBackListsS = g_passBackLists; g_passBackLists = 0;
        g_pddDupS = g_pddDup; g_pddFullS = g_pddFull; g_pddDup = g_pddFull = 0;
        g_worldCallsS = g_worldCalls; g_worldCalls = 0;
        g_omDrawnS = g_omDrawn; g_omDrawn = 0;
        g_omFarAddS = g_omFarAdd; g_omFarAdd = 0;
        g_omFarSkipS = g_omFarSkip; g_omFarSkip = 0;
        g_omFarWalkS = g_omFarWalk; g_omFarWalk = 0;
        g_omFarBadS  = g_omFarBad;  g_omFarBad  = 0;
        g_omFarNoneS = g_omFarNone; g_omFarNone = 0;
        g_farCaughtS = g_farCaught; g_farCaught = 0;
        g_feetLogNS = g_feetLogN; g_feetLogN = 0;
        g_directCallsS = g_directCalls; g_directCalls = 0;
        g_farPurgedS = g_farPurged; g_farPurged = 0;
        g_omLocalRejS = g_omLocalRej; g_omLocalRej = 0;
        g_wedgeSeenS = g_wedgeSeen; g_wedgeSeen = 0;
        g_wedgeDropS = g_wedgeDrop; g_wedgeDrop = 0;
        g_skyCullNS = g_skyCullN; g_skyCullN = 0;
        g_nearCardDropS = g_nearCardDrop; g_nearCardDrop = 0;
        g_wedgeTexS = g_wedgeTex; g_wedgeObjS = g_wedgeObj; g_wedgePassS = g_wedgePass;
        g_wedgeObjYloS = g_wedgeObjYlo; g_wedgeObjYhiS = g_wedgeObjYhi;
        g_wedgeRaiseS = g_wedgeRaise; g_wedgeLowS = g_wedgeLow;
        g_deepDroppedS = g_deepDropped; g_deepDropped = 0;
        g_behindDroppedS = g_behindDropped; g_behindDropped = 0;
        g_omSkippedS = g_omSkipped; g_omSkipped = 0;
        g_passMsOrigS = g_passMsOrig; g_passMsExtraS = g_passMsExtra;
        g_passMsOrig = g_passMsExtra = 0.0;
        g_nonWorldQS = g_nonWorldQ; g_nonWorldQ = 0;
        for (i = 0; i < 6; i++) { g_nwRaS[i] = g_nwRa[i]; g_nwRaNS[i] = g_nwRaN[i]; }
        g_nwNS = g_nwN; g_nwN = 0;
        {
            int a2, b2;
            for (a2 = 0; a2 < 8; a2++) {
                g_passOffAxisS[a2] = g_passOffAxis[a2]; g_passOffAxis[a2] = 0;
                g_passFxS[a2] = g_passFx[a2]; g_passCxS[a2] = g_passCx[a2];
                for (b2 = 0; b2 < 6; b2++) { g_passDirHistS[a2][b2] = g_passDirHist[a2][b2]; g_passDirHist[a2][b2] = 0; }
                if (g_passSampleOk[a2]) {
                    for (b2 = 0; b2 < 7; b2++) { int c2; for (c2 = 0; c2 < 4; c2++) g_passSampleS[a2][b2][c2] = g_passSample[a2][b2][c2]; }
                    g_passSampleOkS[a2] = 1;
                }
                g_passSampleOk[a2] = 0;
            }
            g_passFxSeenS = g_passFxSeen; g_passFxSeen = 0;
        }
        /* With passes off the big block below never ran and there was no log
         * at all. It is not audited for the no-pass state, so it stays gated;
         * a short block of its own carries what the single engine pass needs:
         * the exact line, the distance line and autofar. */
        if (!g_passOn && GetTickCount() - g_passTicks > 2000) {
            HANDLE h;
            g_passTicks = GetTickCount();
            g_afPairsS = g_afPairs; g_afPairs = 0;
            g_afAppliedS = g_afApplied; g_afApplied = 0;
            if (!g_passLogFresh) passLog("");
            h = CreateFileA("VC2VR_PASS.LOG", FILE_APPEND_DATA, FILE_SHARE_READ,
                            NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
            if (h != INVALID_HANDLE_VALUE) {
                char b[4096]; DWORD w; char *p2; int li;
                wsprintfA(b, "exact: clip %d hook %d | tx hit %u miss %u | quads %u | clip poly %u pieces %u | legacy %u\r\n",
                          (int)g_clipState, (int)g_projState, g_txHitS, g_txMissS,
                          g_exQuadsS, g_clipPolyS, g_clipPiecesS, g_legacyQS);
                WriteFile(h, b, lstrlenA(b), &w, NULL);
                p2 = b;
                p2 += wsprintfA(p2, "  dist m:");
                for (li = 0; li < 16; li++)
                    if (g_ldS[li].n)
                        p2 += wsprintfA(p2, " L%d n%u %d..%d", li, g_ldS[li].n,
                                        (int)g_ldS[li].dmin, (int)g_ldS[li].dmax);
                wsprintfA(p2, "\r\n");
                WriteFile(h, b, lstrlenA(b), &w, NULL);
                afLogLine(b);
                WriteFile(h, b, lstrlenA(b), &w, NULL);
                CloseHandle(h);
            }
        }
        if (g_passOn && GetTickCount() - g_passTicks > 2000) {
            HANDLE h;
            g_passTicks = GetTickCount();
            g_afPairsS = g_afPairs; g_afPairs = 0;
            g_afAppliedS = g_afApplied; g_afApplied = 0;
            if (!g_passLogFresh) passLog("");
            h = CreateFileA("VC2VR_PASS.LOG", FILE_APPEND_DATA, FILE_SHARE_READ,
                            NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
            if (h != INVALID_HANDLE_VALUE) {
                char b[4096]; DWORD w;
                /* exact geometry, the line that says whether this build is
                 * doing its job: tx hit/miss should be N/0 in every pass,
                 * bump is the far-vertex fix working, full and exfull must
                 * stay 0, clip is straddling polygons per frame */
                wsprintfA(b, "exact: clip %d hook %d | tx hit %u miss %u badhit %u bent %u bump %u full %u | quads %u dup %u seen %u exfull %u | "
                             "clip poly %u pieces %u held %u deep %u dup %u none %u\r\n",
                          (int)g_clipState, (int)g_projState, g_txHitS, g_txMissS, g_txBadHitS, g_bentDropS, g_txBumpS, g_txFullS,
                          g_exQuadsS, g_exDupS, g_exSeenNS, g_exFullS,
                          g_clipPolyS, g_clipPiecesS, g_clipHeldS, g_clipDeepS, g_clipDupS, g_clipNoRecS);
                WriteFile(h, b, lstrlenA(b), &w, NULL);
                afLogLine(b);
                WriteFile(h, b, lstrlenA(b), &w, NULL);
                {   char *p2 = b; int li;
                    p2 += wsprintfA(p2, "  sky ring %d locked %d phase %d tan %d/%d | up %d %d %d (ok %d level %d) |",
                                    g_skyRing, g_skyLocked, (int)(g_skyPhase * 573.0f),
                                    (int)(g_skyTanT * 100.0f), (int)(g_skyTanB * 100.0f),
                                    (int)(g_upV[0] * 1000), (int)(g_upV[1] * 1000),
                                    (int)(g_upV[2] * 1000), g_upOk, g_levelWorld);
                    p2 += wsprintfA(p2, " fail %d scale %d | dome q %u skip %d walk %u,%u held %d miss %d | mtx",
                                    g_upFail, (int)(g_upScale * 1000),
                                    g_domeQ, g_domeSkip,
                                    g_domeWalk[0], g_domeWalk[1],
                                    g_skyHeld, g_skyMiss);
                    {   int q2;
                        for (q2 = 0; q2 < 12; q2++)
                            p2 += wsprintfA(p2, "%s %d", (q2 % 3) ? "" : " |",
                                            (int)(g_upRow[q2] * 1000));
                    }
                    p2 += wsprintfA(p2, " |");
                    wsprintfA(p2, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                }
                {   char *p2 = b; int li;
                    p2 += wsprintfA(p2, "  dist m:");
                    for (li = 0; li < 16; li++)
                        if (g_ldS[li].n)
                            p2 += wsprintfA(p2, " L%d n%u %d..%d", li, g_ldS[li].n,
                                            (int)g_ldS[li].dmin, (int)g_ldS[li].dmax);
                    p2 += wsprintfA(p2, " | widest tex %u %dm2 at %dm (sr %d) | biggest %dm2 tex %u at %dm\r\n",
                                    g_wideTexS, (int)g_wideAreaS, (int)g_wideDistS,
                                    (int)(g_wideSrS * 100.0f),
                                    (int)g_bigAreaS, g_bigTexS, (int)g_bigDistS);
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                }
                {   char *p2 = b; int li;
                    p2 += wsprintfA(p2, "  atsprdist %u biggest tex %u %dx%d sentfar %u | legacy %u by layer:",
                                    g_farSprS, g_farSprTexS,
                                    (int)g_farSprWS, (int)g_farSprHS, g_bigMissS, g_legacyQS);
                    for (li = 0; li < 16; li++)
                        if (g_legacyLS[li]) p2 += wsprintfA(p2, " l%d=%u", li, g_legacyLS[li]);
                    wsprintfA(p2, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                }
                wsprintfA(b, "cam %d world %d wcalls %u | seen/kept front %u/%u back %u/%u left %u/%u "
                             "right %u/%u up %u/%u down %u/%u xfront %u/%u | backlists %u "
                             "quads %u | dedup dup %u full %u\r\n",
                          (int)g_camState, (int)g_worldState, g_worldCallsS,
                          g_passSeenS[0], g_passKeptS[0], g_passSeenS[1], g_passKeptS[1],
                          g_passSeenS[2], g_passKeptS[2], g_passSeenS[3], g_passKeptS[3],
                          g_passSeenS[4], g_passKeptS[4], g_passSeenS[5], g_passKeptS[5],
                          g_passSeenS[6], g_passKeptS[6], g_passBackListsS,
                          (unsigned)(g_buildCount / 6), g_pddDupS, g_pddFullS);
                WriteFile(h, b, lstrlenA(b), &w, NULL);
                {
                    char *p2 = b; int ki, kn = (int)g_pddKillN; if (kn > 8) kn = 8;
                    p2 += wsprintfA(p2, "  dedupkill %d:", kn);
                    for (ki = 0; ki < kn; ki++)
                        p2 += wsprintfA(p2, " [tex %u p%d cand %d,%d,%d ate p%d at %d,%d,%d d%d t%d w%u]",
                            g_pddKill[ki].tex, g_pddKill[ki].cpass,
                            (int)g_pddKill[ki].cc[0], (int)g_pddKill[ki].cc[1], (int)g_pddKill[ki].cc[2],
                            g_pddKill[ki].epass,
                            (int)g_pddKill[ki].ec[0], (int)g_pddKill[ki].ec[1], (int)g_pddKill[ki].ec[2],
                            (int)g_pddKill[ki].dist, (int)(g_pddKill[ki].tol * 10.0f), g_pddKill[ki].w0);
                    p2 += wsprintfA(p2, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                    g_pddKillN = 0;
                }
                {   /* cross-pass matches with unequal centroids: the offline
                     * reproduction has none, so these ARE the false matches */
                    char *p2 = b; int ki, kn = (int)g_pddXKillN; if (kn > 8) kn = 8;
                    p2 += wsprintfA(p2, "  dedupxkill %d:", kn);
                    for (ki = 0; ki < kn; ki++)
                        p2 += wsprintfA(p2, " [tex %u p%d cand %d,%d,%d ate p%d at %d,%d,%d d%d t%d w%u]",
                            g_pddXKill[ki].tex, g_pddXKill[ki].cpass,
                            (int)g_pddXKill[ki].cc[0], (int)g_pddXKill[ki].cc[1], (int)g_pddXKill[ki].cc[2],
                            g_pddXKill[ki].epass,
                            (int)g_pddXKill[ki].ec[0], (int)g_pddXKill[ki].ec[1], (int)g_pddXKill[ki].ec[2],
                            (int)g_pddXKill[ki].dist, (int)(g_pddXKill[ki].tol * 10.0f), g_pddXKill[ki].w0);
                    {
                        int sl, shift = 0;
                        for (sl = 1; sl < 8; sl++)
                            if ((g_passFxSeenS & (1u << sl)) && (g_passFxSeenS & 1u) &&
                                (g_passFxS[sl] != g_passFxS[0] || g_passCxS[sl] != g_passCxS[0]))
                                shift |= (1 << sl);
                        p2 += wsprintfA(p2, " | offaxis b%u l%u r%u u%u d%u | fx0 %d cx0 %d shift %02X",
                            g_passOffAxisS[1], g_passOffAxisS[2], g_passOffAxisS[3],
                            g_passOffAxisS[4], g_passOffAxisS[5],
                            (int)g_passFxS[0], (int)g_passCxS[0], shift);
                    }
                    p2 += wsprintfA(p2, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                    g_pddXKillN = 0;
                }
                {
                    BYTE *base = (BYTE *)GetModuleHandleA(NULL);
                    DWORD skip = 0, skipN = 0, lat = 0;
                    int k; char *p = b;
                    if (base && !IsBadReadPtr(base + 0x12B8C0, 4)) skip = *(DWORD *)(base + 0x12B8C0);
                    if (base && !IsBadReadPtr(base + 0x0CEB94, 4)) skipN = *(DWORD *)(base + 0x0CEB94);
                    if (base && !IsBadReadPtr(base + 0x12B890, 4)) lat = *(DWORD *)(base + 0x12B890);
                    p += wsprintfA(p, "  memory %u objects, drawn %u skipped %u /pass-frame, purged %u resets %u (hook %d) sweeps %u killed %u stale %u | ",
                                   g_omN, g_omDrawnS, g_omSkippedS, g_omPurged, g_omResets, (int)g_resetState, g_omSwept, g_omKilled, g_omBad);
                    p += wsprintfA(p, "omcull %d fwd %d.%d omfar %d new %u refused %u walk %u bad %u empty %u ahead %d farhook %d caught %u passa %d | ",
                                   g_omCull, (int)g_omFwd, ((int)(g_omFwd * 10)) % 10,
                                   g_omFar, g_omFarAddS, g_omFarSkipS,
                                   g_omFarWalkS, g_omFarBadS, g_omFarNoneS, g_cityAhead,
                                   (int)g_chunkState, g_farCaughtS, g_passA);
                    p += wsprintfA(p, "lifedec %d farown %u purged %u omlocal %d rej %u | ",
                                   g_lifeDecState, g_farOwnN, g_farPurgedS,
                                   g_omLocal, g_omLocalRejS);
                    p += wsprintfA(p, "wedge seen %u drop %u skycull %u nearcard %u p%u tex %u obj %08X objY %d..%d raise %d low %d | ",
                                   g_wedgeSeenS, g_wedgeDropS, g_skyCullNS, g_nearCardDropS, g_wedgePassS, g_wedgeTexS, g_wedgeObjS,
                                   (int)g_wedgeObjYloS, (int)g_wedgeObjYhiS,
                                   (int)g_wedgeRaiseS, (int)g_wedgeLowS);
                    p += wsprintfA(p, "ms orig %d.%d extra %d.%d | skipflag %u skipcount %u late %u | nonworld %u from",
                                   (int)g_passMsOrigS, (int)(g_passMsOrigS * 10) % 10,
                                   (int)g_passMsExtraS, (int)(g_passMsExtraS * 10) % 10,
                                   skip, skipN, lat, g_nonWorldQS);
                    for (k = 0; k < g_nwNS; k++) p += wsprintfA(p, " %08X:%u", g_nwRaS[k], g_nwRaNS[k]);
                    wsprintfA(p, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                }
                {   /* [probe] splash ray */
                    char *p = b; int k;
                    p += wsprintfA(p, "  nearclip: dropped %d rep1 %d rep2 %d (w0 %d rhw0 %d centre %d) neardrop %d | nearown %d skip %d | deepdrop %d killed %u | behinddrop %d killed %u | trueclip %d splitdepth %d clampdrop %d groundfill %d\r\n", (int)g_nearDropped, (int)g_nearRep1, (int)g_nearRep2, (int)g_nearW0, (int)g_nearRhw0, (int)g_nearCentre, g_nearDrop, (int)g_nearOwn, (int)g_nearOwnSkip,
                                   g_deepDrop, g_deepDroppedS, g_behindDrop, g_behindDroppedS,
                                   g_trueClip, g_splitDepth, g_clampDrop, g_groundFill);
                    if (g_pdN) {
                        int pd;
                        for (pd = 0; pd < g_pdN; pd++)
                            WriteFile(h, g_pdBuf[pd], lstrlenA(g_pdBuf[pd]), &w, NULL);
                        g_pdN = 0;
                    }
                    g_nearDropped = g_nearRep1 = g_nearRep2 = 0;
                    g_nearW0 = g_nearRhw0 = g_nearCentre = g_nearOwnSkip = 0;
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                    if (g_floorProbe) floorProbeLog(h);
                    if (!g_passLogVerbose) goto logdone;
                    p = b;
                    p += wsprintfA(p, "  splash: try %u hit %u miss %u noworld %u |", g_spTry, g_spHit, g_spMiss, g_spNoWorld);
                    for (k = 0; k < 8; k++) {
                        int j = (g_spSW - 1 - k) & 7;
                        if (!g_spS[j].tex) continue;
                        p += wsprintfA(p, " [tex %u p%d b%d nb %u tri %u t %d m %d,%d]", g_spS[j].tex, g_spS[j].prio, g_spS[j].base,
                                       g_spS[j].nb, g_spS[j].ntri, (int)g_spS[j].t, (int)g_spS[j].mx, (int)g_spS[j].my);
                    }
                    p += wsprintfA(p, " | skystage %u", g_skS);
                    for (k = 0; k < 8; k++) {
                        int j = (g_skW - 1 - k) & 7;
                        if (!g_skR[j].tex) continue;
                        p += wsprintfA(p, " [tex %u %d,%d-%d,%d sh %d]", g_skR[j].tex, (int)g_skR[j].x0, (int)g_skR[j].y0,
                                       (int)g_skR[j].x1, (int)g_skR[j].y1, g_skR[j].sh);
                    }
                    wsprintfA(p, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                    p = b;
                    p += wsprintfA(p, "  bigquad %u", g_bqS);
                    for (k = 0; k < 8; k++) {
                        int j = (g_bqW - 1 - k) & 7;
                        if (!g_bqR[j].id && !g_bqR[j].w) continue;
                        p += wsprintfA(p, " [id %u w %u col %08X %d,%d-%d,%d]", g_bqR[j].id, g_bqR[j].w, g_bqR[j].col,
                                       g_bqR[j].x0, g_bqR[j].y0, g_bqR[j].x1, g_bqR[j].y1);
                    }
                    wsprintfA(p, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                    p = b;
                    p += wsprintfA(p, "  newnw %u", g_nnS);
                    for (k = 0; k < 16; k++) {
                        int j = (g_nnW - 1 - k + 32) % 16;
                        if (!g_nnR[j].id && !g_nnR[j].w) continue;
                        p += wsprintfA(p, " [id %u w %u c %d,%d %dx%d +%dms aim %d,%d]", g_nnR[j].id, g_nnR[j].w,
                                       g_nnR[j].cx, g_nnR[j].cy, g_nnR[j].wd, g_nnR[j].ht, g_nnR[j].dt, g_nnR[j].xx, g_nnR[j].xy);
                    }
                    wsprintfA(p, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                    p = b;
                    p += wsprintfA(p, "  nearaim %u", g_naS);
                    for (k = 0; k < 16; k++) {
                        int j = (g_naW - 1 - k + 32) % 16;
                        if (!g_naR[j].id && !g_naR[j].w) continue;
                        p += wsprintfA(p, " [%s id %u w %u p%d c %d,%d %dx%d +%dms aim %d,%d iw %d]", g_naR[j].kind ? "SPR" : "QUAD",
                                       g_naR[j].id, g_naR[j].w, g_naR[j].prio, g_naR[j].cx, g_naR[j].cy, g_naR[j].wd, g_naR[j].ht,
                                       g_naR[j].dt, g_naR[j].ax, g_naR[j].ay, g_naR[j].inw);
                    }
                    wsprintfA(p, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                    p = b;
                    p += wsprintfA(p, "  smallspr %u", g_ssS);
                    for (k = 0; k < 12; k++) {
                        int j = (g_ssW - 1 - k + 24) % 12;
                        if (!g_ssR[j].tex) continue;
                        p += wsprintfA(p, " [tex %u p%d %d,%d-%d,%d]", g_ssR[j].tex, g_ssR[j].prio,
                                       g_ssR[j].x0, g_ssR[j].y0, g_ssR[j].x1, g_ssR[j].y1);
                    }
                    wsprintfA(p, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                }
                {   /* stream structure: sections, records, where the cursor is */
                    BYTE *base = (BYTE *)GetModuleHandleA(NULL);
                    char *p = b;
                    if (base) {
                        DWORD *pairs = *(DWORD **)(base + (EXE_PAIRS - 0x00400000));
                        DWORD *curB = *(DWORD **)(base + (EXE_CUR_B - 0x00400000));
                        DWORD *curA = *(DWORD **)(base + (EXE_CUR_A - 0x00400000));
                        int idx = *(short *)(base + (EXE_SECTION - 0x00400000));
                        int k;
                        p += wsprintfA(p, "  streams: section %d pairs %08X curB %08X curA %08X progress %u |",
                                       idx, (DWORD)(DWORD_PTR)pairs, (DWORD)(DWORD_PTR)curB,
                                       (DWORD)(DWORD_PTR)curA, (unsigned)*(WORD *)(base + 0xDB8B8));
                        for (k = 0; k < 12 && pairs && !IsBadReadPtr(pairs + k * 2, 8); k++) {
                            DWORD *r = (DWORD *)(DWORD_PTR)pairs[k * 2];
                            DWORD *ra = (DWORD *)(DWORD_PTR)pairs[k * 2 + 1];
                            int n = 0, na = 0;
                            if (!r) break;
                            while (n < 64 && !IsBadReadPtr(r + n * 2, 8) && (LONG)r[n * 2 + 1] != -1) n++;
                            while (ra && na < 64 && !IsBadReadPtr(ra + na * 2, 8) && (LONG)ra[na * 2 + 1] != -1) na++;
                            p += wsprintfA(p, " s%d:B@%08X n%d(k%u..%u) A@%08X n%d", k,
                                           (DWORD)(DWORD_PTR)r, n, n ? r[1] : 0, n ? r[(n - 1) * 2 + 1] : 0,
                                           (DWORD)(DWORD_PTR)ra, na);
                            if (p - b > 800) break;
                        }
                        wsprintfA(p, "\r\n");
                        WriteFile(h, b, lstrlenA(b), &w, NULL);
                    }
                }
                {   /* centroid directions of the kept quads, per pass */
                    static const char *nm[7] = { "front", "back", "left", "right", "up", "down", "xfront" };
                    int a2; char *p = b;
                    p += wsprintfA(p, "  centroids F/B/L/R/U/D:");
                    for (a2 = 0; a2 < 7; a2++) {
                        if (!g_passKeptS[a2]) continue;
                        p += wsprintfA(p, " %s=%u/%u/%u/%u/%u/%u", nm[a2],
                            g_passDirHistS[a2][0], g_passDirHistS[a2][1], g_passDirHistS[a2][2],
                            g_passDirHistS[a2][3], g_passDirHistS[a2][4], g_passDirHistS[a2][5]);
                    }
                    wsprintfA(p, "\r\n");
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                    for (a2 = 0; a2 < 7; a2++) {
                        int c2; p = b;
                        if (!g_passSampleOkS[a2]) continue;
                        g_passSampleOkS[a2] = 0;
                        p += wsprintfA(p, "  sample %s:", nm[a2]);
                        for (c2 = 0; c2 < 4; c2++)
                            p += wsprintfA(p, " [sx %d sy %d w %d -> %d %d %d]",
                                (int)g_passSampleS[a2][0][c2], (int)g_passSampleS[a2][1][c2],
                                (int)g_passSampleS[a2][2][c2], (int)g_passSampleS[a2][3][c2],
                                (int)g_passSampleS[a2][4][c2], (int)g_passSampleS[a2][5][c2]);
                        wsprintfA(p, "\r\n");
                        WriteFile(h, b, lstrlenA(b), &w, NULL);
                    }
                }
            logdone:
                CloseHandle(h);
            }
        }
    }
    afFrame();
    pushSkyDome();
    pushGround();
    pushFeetFill();
    g_skyN = 0;
    g_sxMinS = g_sxMin; g_sxMaxS = g_sxMax;
    g_syMinS = g_syMin; g_syMaxS = g_syMax;
    g_sxMin = g_syMin = 1e9f; g_sxMax = g_syMax = -1e9f;
    /* the engine draws with no z-buffer at all (ZENABLE 0 at 0x10001FFF): it
     * radix sorts the frame by the per quad key and paints from the largest
     * key - the farthest - downwards. Reproduce that order here; equal keys
     * keep their submission order, which is what the radix sort does too. */
    g_ammoIdS[0] = g_ammoId[0]; g_ammoIdS[1] = g_ammoId[1];
    g_lifeNS[0] = g_lifeN[0];   g_lifeNS[1] = g_lifeN[1];
    g_ammoId[0] = g_ammoId[1] = 0;
    g_lifeN[0] = g_lifeN[1] = 0;
    hudDrawOwn();
    {
        UINT nq = g_buildCount / 6, k, o = 0;
        if (nq > MAX_QUADS) nq = MAX_QUADS;
        if (nq > 1) {
            for (k = 0; k < nq; k++)
                g_sortKey[k] = ((0xFFFFFFFFFull - g_quadKey[k]) << 20) |
                               (unsigned __int64)(k & 0xFFFFF);
            qsort(g_sortKey, nq, sizeof(g_sortKey[0]), cmp64);
            /* two stable passes over the sorted order: everything that lives
             * in the world first, the flat overlay after it. Overlay already
             * sorted to the tail (keys 0..2 are the smallest), so this moves
             * nothing except past the hit splash, which is a world event that
             * happens to share priority 2 - and the HUD belongs on top of it
             * anyway. */
            for (k = 0; k < nq; k++) {
                UINT q = (UINT)(g_sortKey[k] & 0xFFFFF);
                if (g_quadFlat[q]) continue;
                CopyMemory(g_draw + (SIZE_T)o * 6, g_build + (SIZE_T)q * 6,
                           6 * sizeof(Vtx));
                o++;
            }
            g_ovStart = o * 6;
            for (k = 0; k < nq; k++) {
                UINT q = (UINT)(g_sortKey[k] & 0xFFFFF);
                if (!g_quadFlat[q]) continue;
                CopyMemory(g_draw + (SIZE_T)o * 6, g_build + (SIZE_T)q * 6,
                           6 * sizeof(Vtx));
                o++;
            }
        } else {
            CopyMemory(g_draw, g_build, g_buildCount * sizeof(Vtx));
            g_ovStart = (nq == 1 && g_quadFlat[0]) ? 0 : g_buildCount;
        }
    }
    g_drawCount = g_buildCount;
    g_prevKey = 0;
    CopyMemory(g_mtxDump, g_mtx, sizeof(g_mtxDump));
    g_mtxDumpN = g_mtxN;
    g_mtxTotalS = g_mtxTotal;
    g_mtxN = 0;
    g_mtxTotal = 0;
    CopyMemory(g_sprDump, g_sprInfo, sizeof(g_sprDump));
    g_sprShownN = g_sprN2;
    {   /* The two debug knobs are re-read from the ini once a second, so a
         * mode can be changed while the headset is on and the level is
         * running. Everything else still needs a restart; these two exist
         * only to be poked at, and a restart per poke costs a minute of
         * getting back to the place where the artefact is. */
        static DWORD cfgAt;
        DWORD nowc = GetTickCount();
        if (nowc - cfgAt > 1000) {
            cfgAt = nowc;
            g_distDebug = (int)cfgNum("distdebug", 0);
            g_aimProbe  = (int)cfgNum("aimprobe", 0);
            g_farLayers = cfgNum("farlayers", 0);
            g_farScale  = cfgInt("farscale", 800);
            g_nwRadial  = cfgInt("nwradial", 1);
            g_autoFar   = cfgInt("autofar", 1);
            g_afMin     = cfgInt("autofarmin", 15);
            g_afRatio   = cfgInt("autofarratio", 20);
            if (g_afRatio < 1) g_afRatio = 1;
            if (g_afRatio > 90) g_afRatio = 90;
            g_farAuto      = cfgInt("farlayerauto", 1);
            g_farAutoCount = cfgInt("farautocount", 40);
            g_farAutoNear  = cfgInt("farautonear", 12);
            /* the overlay knobs too: getting a HUD to sit right is a dozen
             * small adjustments, and a restart between each of them is what
             * makes people stop after the second one */
            g_hudSpread = (int)cfgNum("hudspread", 100);
            g_hudScale  = (int)cfgNum("hudscale", 100);
            g_hideXhair = (int)cfgNum("hidexhair", 1);
            g_sprDist   = (float)cfgNum("sprdist", 312);
            g_hudHideN  = cfgRanges("hudhide", g_hudHide, IDR_MAX);
            g_panelIdsN = cfgRanges("panelids", g_panelIds, IDR_MAX);
            g_panelDist = cfgInt("paneldist", 110);
            g_panelDrop = cfgInt("paneldrop", 60);
            g_panelScale= cfgInt("panelscale", 100);
            g_hudLog    = cfgInt("hudlog", 0);
            g_hudOwn    = cfgInt("hudown", 0);
            g_hudOwnSize= cfgInt("hudownsize", 100);
            g_hudLives  = cfgInt("hudlives", 0);
            /* the sky knobs, live from now on. Every sky question so far has
             * cost a game restart and the place where the artefact was. */
            g_skyDome   = cfgInt("skydome", 1);
            g_skyLock   = cfgInt("skylock", 1);
            g_skyCap    = cfgInt("skycap", 1);
            g_levelWorld= cfgInt("levelworld", 1);
            g_skyDebug  = cfgInt("skydebug", 0);
            g_skyHold   = cfgInt("skyhold", 600);
            g_sprFar    = (float)cfgNum("sprfar", 90000);
            /* the pass knobs, live. Bisecting a 360-degree artefact one
             * restart at a time is what makes it take a session instead of
             * a minute. "passes" itself installs hooks and stays init-only. */
            g_passA      = cfgInt("passa", 0);
            g_passB      = cfgInt("passb", 1);
            g_passUpDown = cfgInt("passupdown", 1);
            g_passDedup  = cfgInt("passdedup", 0);
            g_passTol    = cfgInt("passtol", 3);
            g_cityMemory = cfgInt("citymemory", 1);
            g_cityRadius = (float)cfgNum("cityradius", 15000);
            g_omCap      = cfgInt("citymax", 2500);
            g_omCull     = cfgInt("omcull", 1);
            /* how many chunks of track ahead are handed to the engine's own
             * pass and, with them, learnt into the object memory. The old
             * "above 2 crashes" is gone - that was the 3000-quad wall in
             * HGL_D3D, and quadcap holds it now - so this is a real knob, and
             * a live one: a structure the memory has not learnt yet is a
             * structure no rotated pass can draw, and sweeping this is the
             * fastest way to tell "not learnt yet" from "lost". */
            g_cityAhead  = cfgInt("cityahead", 2);
            if (g_cityAhead < 0)  g_cityAhead = 0;
            if (g_cityAhead > 64) g_cityAhead = 64;
            /* the geometry knobs, live. Each is read at the point of use, and
             * bisecting a torn surface one restart at a time is what costs a
             * session. */
            g_trueClip   = cfgInt("trueclip", 1);
            g_splitDepth = cfgInt("splitdepth", 0x20);
            if (g_splitDepth < 2) g_splitDepth = 2;
            if (g_splitDepth > 0x20) g_splitDepth = 0x20;
            g_clampDrop  = cfgInt("clampdrop", 1);
            g_nearDrop   = cfgInt("neardrop", 1);
            g_groundFill = cfgInt("groundfill", 0);
            g_floorProbe = cfgInt("floorprobe", 0);
            g_shotLog    = cfgInt("shotlog", 0);
            g_aimProbe   = cfgInt("aimprobe", 0);
            g_feetFill   = cfgInt("feetfill", 0);
            g_feetDrop   = cfgInt("feetdrop", 3);
            g_deepDrop   = cfgInt("deepdrop", 0);
            g_passDump   = cfgInt("passdump", 0);
            g_dumpY      = cfgInt("dumpy", 0);
            g_passDumpN  = cfgInt("passdumpn", 40);
            if (g_passDumpN < 1) g_passDumpN = 1;
            if (g_passDumpN > PDUMP_MAX) g_passDumpN = PDUMP_MAX;
            g_behindDrop = cfgInt("behinddrop", 0);
            g_pvFollow   = cfgInt("previewfollow", 1);
            g_pvZoom     = cfgInt("previewzoom", 130);
            g_omFar      = cfgInt("omfar", 1);
            g_omLocal    = cfgInt("omlocal", 1);
            g_wedgeFix   = cfgInt("wedgefix", 1);
            g_wedgeHi    = cfgInt("wedgehi", 600);
            g_nearDropX  = cfgInt("neardropx", 1);
            g_skyCull    = cfgInt("skycull", 1);
            g_skyHi      = cfgInt("skyhi", 3000);
            g_skyDist    = cfgInt("skydist", 16000);
            g_noLifeDec  = cfgInt("nolifedec", 0);
            lifeDecApply();
            g_cityBack   = cfgInt("cityback", 0);
            g_nearOwn    = (float)cfgNum("nearown", 800);
            if (g_hudSpread < 20) g_hudSpread = 20;
            if (g_hudSpread > 400) g_hudSpread = 400;
            if (g_hudScale < 20) g_hudScale = 20;
            if (g_hudScale > 400) g_hudScale = 400;
            if (g_panelScale < 20) g_panelScale = 20;
            if (g_panelScale > 400) g_panelScale = 400;
        }
    }
    if (g_hudLog) {
        /* Every overlay sprite of this frame, by id, with its screen box.
         * The overlay is a fixed cast of a dozen or so textures and the ids
         * never move, so one look at this names the drum, the hearts, the
         * credits line and anything else worth drawing ourselves - no
         * guessing from sizes, no scanning memory. Once every two seconds,
         * which is a handful of lines a minute. */
        static DWORD hudAt;
        DWORD nowh = GetTickCount();
        if (nowh - hudAt > 2000 && g_sprShownN) {
            HANDLE h; DWORD wr; char b[2048]; char *p3 = b; int k;
            hudAt = nowh;
            p3 += wsprintfA(p3, "hud n %u:", g_sprShownN);
            for (k = 0; k < (int)g_sprShownN && k < 28; k++)
                p3 += wsprintfA(p3, " [%u p%d %d,%d-%d,%d]",
                                g_sprDump[k].tex, g_sprDump[k].prio,
                                (int)g_sprDump[k].x0, (int)g_sprDump[k].y0,
                                (int)g_sprDump[k].x1, (int)g_sprDump[k].y1);
            p3 += wsprintfA(p3, "\r\n");
            h = CreateFileA("VC2VR_PASS.LOG", FILE_APPEND_DATA, FILE_SHARE_READ,
                            NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
            if (h != INVALID_HANDLE_VALUE) {
                WriteFile(h, b, lstrlenA(b), &wr, NULL);
                CloseHandle(h);
            }
        }
    }
    if (g_aimProbe) {
        DWORD nowa = GetTickCount();
        if (g_aimArm) {                 /* the frame we armed has been walked */
            HANDLE h; DWORD wr; char b[8192]; char *p2 = b; int k, n = (int)g_aimN;
            g_aimArm = 0;
            if (n > AIM_MAX) n = AIM_MAX;
            p2 += wsprintfA(p2, "aim %d,%d fx %d quads %d\r\n",
                            g_share ? (int)g_share->aim_x : -1,
                            g_share ? (int)g_share->aim_y : -1, (int)g_fx, n);
            if (g_share) {      /* sprites whose box holds the aim: the floaters */
                float ax = g_share->aim_x, ay = g_share->aim_y;
                for (k = 0; k < (int)g_sprShownN && k < 32; k++) {
                    const SprInfo *si = &g_sprDump[k];
                    int hold = ax >= si->x0 - 2 && ax <= si->x1 + 2 && ay >= si->y0 - 2 && ay <= si->y1 + 2;
                    p2 += wsprintfA(p2, "  spr tex %u p%d box %d,%d-%d,%d%s\r\n", si->tex, si->prio,
                                    (int)si->x0, (int)si->y0, (int)si->x1, (int)si->y1,
                                    hold ? "  <-- UNDER THE AIM" : "");
                }
            }
            for (k = 0; k < n; k++) {
                AimRec *a = &g_aim[k];
                p2 += wsprintfA(p2,
                    "  tex %u L%d %s true%d ours %dm engine %d %d %d %d m"
                    " box %d,%d-%d,%d flags %08X ra %06X\r\n",
                    a->tex, a->layer,
                    a->path == 0 ? "world" : a->path == 1 ? "NONWORLD" : "pass",
                    a->trueN, (int)a->dm,
                    (int)a->zm[0], (int)a->zm[1], (int)a->zm[2], (int)a->zm[3],
                    a->x0, a->y0, a->x1, a->y1, a->flags, a->ra);
            }
            h = CreateFileA("VC2VR_PASS.LOG", FILE_APPEND_DATA, FILE_SHARE_READ,
                            NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
            if (h != INVALID_HANDLE_VALUE) {
                WriteFile(h, b, lstrlenA(b), &wr, NULL);
                CloseHandle(h);
            }
        } else if (g_share && g_fireTick != g_aimLast && nowa - g_fireTick < 250) {
            g_aimLast = g_fireTick;     /* one capture per trigger pull */
            g_aimN = 0;
            g_aimArm = 1;
        }
    }
    {   /* [probe] every sprite of every frame in the 400 ms after the trigger */
        DWORD now = GetTickCount();
        /* shotlog = 1: 400 ms after the trigger, as before. shotlog > 1: that
         * many milliseconds - one pull, several seconds of every sprite in
         * every frame, so a thing that comes and goes is caught in the act. */
        if (g_shotLog && g_share && now - g_fireTick < (DWORD)(g_shotLog > 1 ? g_shotLog : 400)) {
            static int shotFrames; static DWORD lastFire;
            HANDLE h; DWORD w; char b[2048]; char *p = b; int k;
            if (lastFire != g_fireTick) { lastFire = g_fireTick; shotFrames = 0; }
            if (shotFrames++ < 1200) {
                p += wsprintfA(p, "shot+%ums aim %d,%d fx %d n %d:", now - g_fireTick,
                               (int)g_share->aim_x, (int)g_share->aim_y, (int)g_fx, (int)g_sprN2);
                for (k = 0; k < (int)g_sprN2 && k < 32; k++)
                    p += wsprintfA(p, " [%u p%d %d,%d-%d,%d]", g_sprInfo[k].tex, g_sprInfo[k].prio,
                                   (int)g_sprInfo[k].x0, (int)g_sprInfo[k].y0, (int)g_sprInfo[k].x1, (int)g_sprInfo[k].y1);
                wsprintfA(p, "\r\n");
                h = CreateFileA("VC2VR_SHOT.LOG", FILE_APPEND_DATA, FILE_SHARE_READ, NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
                if (h != INVALID_HANDLE_VALUE) { WriteFile(h, b, lstrlenA(b), &w, NULL); CloseHandle(h); }
            }
        }
    }
    g_sprN2 = 0;
    {
        int si;
        for (si = 0; si < 4; si++) {
            LONG c = g_sprN[si];
            g_sprShown[si] = c - g_sprPrev[si];
            g_sprPrev[si] = c;
        }
    }
    g_drawAddStart = ~0u;   /* see below: there is no translucent tail */
    g_drawL3End = g_l3End;
    g_cityShown = g_cityExtra;
    g_cityExtra = 0;
    g_quadSentShown = g_quadSent;
    g_quadHeldShown = g_quadHeld;
    g_quadSent = 0;
    g_quadHeld = 0;
    {   UINT nqz = g_buildCount / 6;
        if (nqz > MAX_QUADS) nqz = MAX_QUADS;
        if (nqz) ZeroMemory(g_quadFlat, nqz);
    }
    g_buildCount = 0;
    g_l3End = 0;
    /* This line, together with g_buildCount having just been zeroed, set
     * the start of the "translucent tail" to vertex 0 - so the preview drew
     * the WHOLE frame with additive blending and every surface showed through
     * every other one. That is the ghosting that survived five versions and
     * that no texture rule could explain. HGL_D3D settles the question:
     * vertex alpha is always 0xFF (0x10003F76) and the only transparency in
     * the port is the colour key, so there is no translucent geometry at all
     * and no tail to draw. */
    g_addStart = ~0u;
    g_buildAddN = 0;
    g_buildL3N = 0;
    g_quadKeyN = 0;
    CopyMemory(g_qrDraw, g_qrBuild, g_qrBuildN * sizeof(QRect));
    g_qrDrawN = g_qrBuildN;
    g_qrBuildN = 0;
    g_idHitMinS = g_idHitMin; g_idHitMaxS = g_idHitMax;
    g_idMissMinS = g_idMissMin; g_idMissMaxS = g_idMissMax;
    g_idHitMin = g_idMissMin = ~0u;
    g_idHitMax = g_idMissMax = 0;
    {
        int i;
        for (i = 0; i < MAX_SLOTS; i++) {
            LONG c = g_slotCalls[i];
            g_slotShown[i] = c - g_slotPrev[i];
            g_slotPrev[i] = c;
        }
    }
    g_objScans = 0;
    if (g_probeAt && GetTickCount() < g_probeAt) {
        g_probeN = 0;                       /* keep only the latest frame */
    } else if (g_probeAt && g_probeN) {
        char dir[MAX_PATH], path[MAX_PATH];
        HANDLE f;
        int i;
        lstrcpyA(dir, g_iniPath);
        { int n = lstrlenA(dir); while (n > 0 && dir[n-1] != '\\') n--; dir[n] = 0; }
        lstrcatA(dir, "texdump");
        CreateDirectoryA(dir, NULL);
        wsprintfA(path, "%s\\probe.txt", dir);
        f = CreateFileA(path, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS,
                        FILE_ATTRIBUTE_NORMAL, NULL);
        if (f != INVALID_HANDLE_VALUE) {
            char b[128]; DWORD w;
            #define OUT(...) do { wsprintfA(b, __VA_ARGS__);                                   WriteFile(f, b, lstrlenA(b), &w, NULL); } while (0)
            OUT("quad.texture values this frame (id count):\r\n");
            for (i = 0; i < g_probeN; i++)
                OUT("%u %d\r\n", g_probeId[i], g_probeCnt[i]);
            OUT("\r\ncull patch: state %d at %08X base %08X size %08X hits %d\r\n",
                (int)g_cullState, g_cullAt, g_cullBase, g_cullSpan,
                g_cullFound);
            OUT("projection: live %d fx %d fy %d cx %d cy %d fov %d (ini fx %d)\r\n",
                g_projOk, (int)g_fx, (int)g_fy, (int)g_cx, (int)g_cy,
                (int)g_projFov, (int)g_fxIni);
            OUT("city extension (0x440D69): state %d ahead %d extra lists %d\r\n",
                (int)g_cityState, g_cityAhead, g_cityShown);
            OUT("quads: submitted %d, held back from HGL_D3D %d (cap %d of 3000)\r\n",
                g_quadSentShown, g_quadHeldShown, g_quadCap);
            OUT("widest quad ever seen: %d px, texture %u, flags %08X, from %08X\r\n",
                (int)g_wideMax, g_wideTex, g_wideFlags, g_wideFrom);
            OUT("saturated quads dropped so far: %d (clampdrop %d)\r\n",
                (int)g_clampDropped, g_clampDrop);
            OUT("ground fill: on %d, called %d, emitted %d, no room %d, textured %d\r\n",
                g_groundFill, g_groundCalls, g_groundEmitted, g_groundFail,
                g_groundHadTex);
            OUT("  groundy %d size %d tex %d tile %d, build %u of %u\r\n",
                (int)g_groundY, (int)g_groundSize, (int)g_groundTex,
                (int)g_groundTile, g_drawCount, (UINT)(MAX_QUADS * 6));
            OUT("\r\nthree widest quads of the session:\r\n");
            for (i = 0; i < TOPQ; i++) {
                int c;
                if (g_topW[i] <= 0.0f) continue;
                OUT("  %d px tex %u flags %08X from %08X\r\n",
                    (int)g_topW[i], g_top[i].tex, g_top[i].flags, g_top[i].from);
                for (c = 0; c < 4; c++)
                    OUT("     sx %d sy %d w %u (layer %u depth %u)\r\n",
                        (int)g_top[i].sx[c], (int)g_top[i].sy[c], g_top[i].w[c],
                        g_top[i].w[c] / LAYER,
                        g_top[i].w[c] - (g_top[i].w[c] / LAYER) * LAYER);
            }
            OUT("object cull patch (0x440A70): state %d at %08X hits %d\r\n",
                (int)g_ocullState, g_ocullAt, g_ocullFound);
            OUT("model asked for by %08X (rva %08X), model at %08X\r\n",
                g_objDirect, g_objDirect ? g_objDirect - g_cullBase : 0,
                g_objDirectObj);
            {   /* what is actually in memory where the file said it would be */
                const BYTE *pk = (const BYTE *)(DWORD_PTR)(g_cullBase + 0x42500);
                char line[128];
                int k, n2 = 0;
                line[0] = 0;
                if (!IsBadReadPtr(pk, 24))
                    for (k = 0; k < 24; k++) {
                        wsprintfA(line + n2, "%02X", pk[k]);
                        n2 += 2;
                    }
                OUT("bytes at base+42500: %s\r\n", line[0] ? line : "unreadable");
                {
                    char mp[MAX_PATH];
                    mp[0] = 0;
                    GetModuleFileNameA(GetModuleHandleA(NULL), mp, MAX_PATH);
                    OUT("main module: %s\r\n", mp);
                }
            }
            OUT("\r\ntransforms this frame (%d quads, %d distinct%s):\r\n",
                g_mtxTotalS, g_mtxDumpN, g_mtxDumpN >= 12 ? "+" : "");
            for (i = 0; i < g_mtxDumpN; i++) {
                const float *m = g_mtxDump[i].m;
                OUT("  n=%-5d basis %d %d %d | %d %d %d | %d %d %d  pos %d %d %d\r\n",
                    g_mtxDump[i].n,
                    (int)(m[0] * 1000), (int)(m[1] * 1000), (int)(m[2] * 1000),
                    (int)(m[3] * 1000), (int)(m[4] * 1000), (int)(m[5] * 1000),
                    (int)(m[6] * 1000), (int)(m[7] * 1000), (int)(m[8] * 1000),
                    (int)m[9], (int)m[10], (int)m[11]);
            }
            OUT("\r\nwho asked for this model (line 0 is the direct caller):\r\n");
            for (i = 0; i < g_objFromN; i++) {
                char mod[MAX_PATH];
                int sl = 0, c;
                mod[0] = 0;
                GetModuleFileNameA((HMODULE)(DWORD_PTR)g_objFromBase[i],
                                   mod, MAX_PATH);
                for (c = 0; mod[c]; c++) if (mod[c] == 92) sl = c + 1;
                OUT("%2d %08X  base %08X  rva %06X  k%d  %s\r\n", i,
                    g_objFrom[i], g_objFromBase[i],
                    g_objFrom[i] - g_objFromBase[i],
                    g_objFromKind[i], mod + sl);
            }
            OUT("\r\nquad submitters (return addresses):\r\n");
            for (i = 0; i < g_quadFromN; i++) {
                MEMORY_BASIC_INFORMATION mbi;
                char mod[MAX_PATH];
                mod[0] = 0;
                if (VirtualQuery((void *)(DWORD_PTR)g_quadFrom[i], &mbi,
                                 sizeof(mbi)) && mbi.AllocationBase)
                    GetModuleFileNameA((HMODULE)mbi.AllocationBase, mod,
                                       MAX_PATH);
                OUT("%08X base %08X %s\r\n", g_quadFrom[i],
                    (DWORD)(DWORD_PTR)mbi.AllocationBase, mod);
            }
            OUT("\r\nscreen x range submitted: %d .. %d\r\n",
                (int)g_sxMinS, (int)g_sxMaxS);
            OUT("\r\nsprites this frame (tex prio x0 y0 x1 y1):\r\n");
            for (i = 0; i < g_sprShownN && i < 32; i++)
                OUT("%u %d %d %d %d %d\r\n", g_sprDump[i].tex,
                    g_sprDump[i].prio, (int)g_sprDump[i].x0,
                    (int)g_sprDump[i].y0, (int)g_sprDump[i].x1,
                    (int)g_sprDump[i].y1);
            OUT("\r\nquads dropped: dynamic %u, dead variant %u\r\n",
                g_dropDyn, g_dropVar);
            OUT("\r\ntexture upload calls (base count d1min d1max):\r\n");
            for (i = 0; i < g_texCallN; i++)
                OUT("%u %u %u %u\r\n", g_texCalls[i].base, g_texCalls[i].count,
                    g_texCalls[i].d1min, g_texCalls[i].d1max);
            OUT("\r\nslot call deltas per frame:\r\n");
            for (i = 0; i < MAX_SLOTS; i++)
                if (g_slotShown[i]) OUT("slot %d: %d\r\n", i, g_slotShown[i]);
            #undef OUT
            CloseHandle(f);
        }
        g_probeN = 0;
        g_probeAt = 0;
        g_objFromN = 0;
    }
    if (g_doShare) publish(g_draw, g_drawCount);
    LeaveCriticalSection(&g_lock);
    return ((DWORD (__stdcall *)(void *))g_real[SLOT_FLUSH])(arg);
}

/* the game hands its window to the renderer's init slot - catch it there */
static DWORD __stdcall wrap_init(DWORD hInst, DWORD hWnd, DWORD bmp, DWORD info)
{
    g_gameWnd = (HWND)(UINT_PTR)hWnd;
    return ((DWORD (__stdcall *)(DWORD, DWORD, DWORD, DWORD))
            g_real[SLOT_INIT])(hInst, hWnd, bmp, info);
}

/* fallback if init was somehow missed: the biggest visible window we own */
static BOOL CALLBACK findOurWindow(HWND h, LPARAM out)
{
    DWORD pid = 0;
    RECT r;
    GetWindowThreadProcessId(h, &pid);
    if (pid != GetCurrentProcessId() || !IsWindowVisible(h)) return TRUE;
    if (!GetWindowRect(h, &r)) return TRUE;
    if ((r.right - r.left) < 320 || (r.bottom - r.top) < 240) return TRUE;
    *(HWND *)out = h;
    return FALSE;
}

/* ------------------------------------------------- light gun via joystick ---
 *
 * PPJ2DD.EXE reads the light gun ONLY through WinMM's joyGetPosEx. It never
 * reads the mouse (no GetCursorPos anywhere), never reads gameplay keys, and
 * its WndProc (0x0040D950) ignores WM_MOUSE* / WM_KEY* - so the whole SendInput
 * / PostMessage machinery below cannot move the crosshair or pull the trigger.
 * DirectInputCreateA is imported but never called. That is why inject=1 and
 * inject=2 both do nothing for aiming and firing.
 *
 * The fix: HGL_VIEW is already inside the game process, so we IAT-patch the
 * game's joyGetPosEx and joyGetDevCapsA and synthesise a joystick from the VR
 * aim block. No external driver, no vJoy, no focus games.
 *
 * The read path, verified by disassembly (0x00432B0F poll, 0x00432B34..
 * 0x00432E4C decode):
 *
 *     dwXpos/dwYpos live in JOYINFOEX at +0x08/+0x0C, dwButtons at +0x20
 *     deltaX = (dwXpos - centerX[joy]) >> 8            centerX at 0x004CEE50
 *     deltaY = (dwYpos - centerY[joy]) >> 8            centerY at 0x004CEE48
 *     dead zone +-0x10, then *sensitivity (0x004D4263), clamp +-128, +0x7F
 *       -> a 0..255 gun DELTA, 0x7F = no movement
 *     trigger = bit (1 << button_index[joy]) in dwButtons, gun table 0x004D4260
 *
 * The game integrates that delta as a VELOCITY (0x0040C210 unpacks it into
 * the controller block, 0x0040C480 integrates - in the EXE, not the stage
 * DLLs), so the analog gun is relative by nature - a straight absolute map
 * only drifts. joymode=1 therefore closes a loop over the game's own
 * crosshair: feed a velocity toward the VR aim point and the crosshair
 * settles on the laser point. Where the crosshair is comes either from its
 * priority-0 sprite (joysrc=0, pushSprite) or from the controller block
 * itself (joysrc=1, xhairFromGame).
 *
 * At init (0x00433340) the poll must return JOYERR_NOERROR and joyGetDevCapsA
 * must succeed; szOEMVxD == "segajoy.vxd" flips the game into the SEGA VxD
 * path (CreateFile+DeviceIoControl, cannot be emulated blind), so we report a
 * DIFFERENT name and pin centerX/centerY = 0x8000 and sensitivity = identity
 * in the game's own globals on every poll.
 */

static int   g_joyGun     = 1;   /* master switch for the joystick hook       */
static int   g_joyForce   = 1;   /* force player 0 onto the analog-gun path   */
static int   g_onePlayer  = 1;   /* NOP the game's player-2 input poll         */
static int   g_akimbo     = 0;   /* ini master switch for two guns            */
int          g_akimboOn   = 0;   /* effective: g_akimbo AND the VR side agrees */
static LONG  g_joyFireBit = 0;   /* dwButtons bit for trigger if game table 0 */
static LONG  g_joyStartBit= 1;   /* dwButtons bit for START (A/X)             */
static LONG  g_joyBackBit  = 2;  /* dwButtons bit for BACK  (B/Y)             */
static int   g_joyInvertY = 0;   /* flip Y if the gun aims upside down        */
static int   g_joySrc     = 0;   /* 0: track the prio-0 sprite, 1: read the
                                  * crosshair straight out of the game's
                                  * controller block (see xhairFromGame)      */
static int   g_joyHooked  = 0;
static BYTE *g_exeBase    = NULL;

#define EXE_RVA(a) (g_exeBase + ((a) - 0x00400000u))

/* The crosshair position without sprite tracking. PPJ2DD keeps a 0x50-byte
 * controller block per player - 0x0052B8D0 (P0), 0x0052B920 (P1), pushed as
 * such at 0x0040BF58/0x0040BF65 - and a player record at 0x004CF1A0 + p*0x44
 * whose byte +1 is 2 while that player is in the game and whose dword +0x0C
 * points at the block. The velocity from the joystick record lands in the
 * block at +0x20/+0x22 (0x0040C210) and the integrator 0x0040C480 turns it
 * into a position at +0x14/+0x16: signed words, cell*8 - 0xA8 + fine for x
 * and cell*8 - 0x70 + fine for y, i.e. a 352x240 space centred on 0. The
 * sprite itself is drawn by 0x0040D330 through 0x00444390 (flags branch
 * 0x00444521), which puts its centre at
 *     sx = cx + x * W / 352        cx = int16 0x004CF80A, W = float 0x0052B8AC
 *     sy = cy + y * H / 240        cy = int16 0x004CF808, H = float 0x0052B8B0
 * (1/352 and 1/240 are the constants at 0x0044DE70/0x0044DE74, W/H are the
 * render size the game got from HGL at 0x0040A5E2). That is exactly the
 * sprite centre pushSprite sees, so the two sources are interchangeable.
 * The descriptor table 0x00459510 pins the textures: P0 draws 1360, P1 1344.
 * Returns 1 and the centre in sprite space when player p is in the game. */
static int xhairFromGame(int p, float *sx, float *sy)
{
    const BYTE  *rec;
    const BYTE  *ctrl;
    const BYTE  *fallback;
    float w, h;
    short cx, cy, x, y;
    if (!g_exeBase || p < 0 || p > 1) return 0;
    rec      = EXE_RVA(0x004CF1A0) + p * 0x44;
    fallback = EXE_RVA(p ? 0x0052B920 : 0x0052B8D0);
    if (IsBadReadPtr(rec, 0x44)) return 0;
    if (rec[1] != 2) return 0;                    /* not playing right now */
    ctrl = *(const BYTE * const *)(rec + 0x0C);
    if (!ctrl || IsBadReadPtr(ctrl, 0x50)) ctrl = fallback;
    w  = *(const float *)EXE_RVA(0x0052B8AC);
    h  = *(const float *)EXE_RVA(0x0052B8B0);
    cx = *(const short *)EXE_RVA(0x004CF80A);
    cy = *(const short *)EXE_RVA(0x004CF808);
    if (!(w > 1.0f && w < 8192.0f) || !(h > 1.0f && h < 8192.0f)) return 0;
    x = *(const short *)(ctrl + 0x14);
    y = *(const short *)(ctrl + 0x16);
    *sx = (float)cx + (float)x * (w / 352.0f);
    *sy = (float)cy + (float)y * (h / 240.0f);
    return 1;
}

/* WinMM ABI - 13 dwords = 0x34, matches the game's dwSize and field reads */
typedef struct {
    DWORD dwSize, dwFlags, dwXpos, dwYpos, dwZpos, dwRpos, dwUpos, dwVpos;
    DWORD dwButtons, dwButtonNumber, dwPOV, dwReserved1, dwReserved2;
} JOYINFOEX_VC;

typedef UINT (WINAPI *joyPosEx_t)(UINT, JOYINFOEX_VC *);
typedef UINT (WINAPI *joyCaps_t)(UINT, void *, UINT);

static joyPosEx_t g_realJoyPos;
static joyCaps_t  g_realJoyCaps;

static UINT WINAPI hookJoyGetPosEx(UINT id, JOYINFOEX_VC *pji)
{
    static unsigned lastSeq[2];
    static DWORD    lastChange[2];
    unsigned seq, btns_in;
    long X, Y;
    int stale, hidx = (id == 1) ? 1 : 0;

    if (!pji) return 0;

    /* pin the game's calibration so our absolute map holds regardless of what
     * it read at startup (these are the game's own globals, we are in-process) */
    if (g_exeBase && id < 4) {
        *(DWORD *)(EXE_RVA(0x004CEE50) + id * 4) = 0x8000;   /* centerX */
        *(DWORD *)(EXE_RVA(0x004CEE48) + id * 4) = 0x8000;   /* centerY */
        *(BYTE  *)(EXE_RVA(0x004D4263) + id * 4) = 2;        /* identity sens */
    }
    /* the VR side declares two guns by setting share->akimbo; honour it only if
     * the ini also allows it. Recomputed each poll so it tracks the app. */
    g_akimboOn = (g_akimbo && g_share && g_share->akimbo);

    /* force the analog-gun handler (device-type selector [0x0048F8A0 + p*4];
     * value 3 = analog gun uJoyID 0, 4 = analog gun uJoyID 1, 5 = digital,
     * 1 = keyboard). The config menu writes this, so re-assert it every poll.
     * Without it the crosshair sits still because a digital handler quantises
     * the axis to 3 zones. Player 0 is always type 3; player 1 only exists in
     * akimbo, and must be type 4 so the game reads it as joystick id 1. */
    if (g_exeBase && g_joyForce) {
        *(DWORD *)EXE_RVA(0x0048F8A0) = 3;
        if (g_akimboOn)
            *(DWORD *)EXE_RVA(0x0048F8A4) = 4;
    }

    seq = !g_share ? 0
        : ((g_akimboOn && id == 1) ? g_share->aim2_seq : g_share->aim_seq);
    if (seq != lastSeq[hidx]) { lastSeq[hidx] = seq; lastChange[hidx] = GetTickCount(); }
    stale = !g_share || (GetTickCount() - lastChange[hidx] > 700);

    if (stale) {
        pji->dwXpos = pji->dwYpos = 0x8000;
        pji->dwZpos = pji->dwRpos = pji->dwUpos = pji->dwVpos = 0x8000;
        pji->dwButtons = 0;
        pji->dwButtonNumber = 0;
        pji->dwPOV = 0xFFFF;
        return 0;                                   /* JOYERR_NOERROR */
    }

    /* Two modes (ini joymode). The analog-gun path integrates the axis as a
     * VELOCITY, so a straight absolute map only drifts ("lazy"). joymode=1 is
     * the feedback loop: read the game's own crosshair (its priority-0 sprite,
     * captured in pushSprite) and feed a velocity toward the VR aim so it
     * settles on the laser point. joymode=0 is the old absolute map, kept as a
     * fallback that at least moves. */
    {
        /* Aim source for THIS gun. In akimbo, id 1 reads the second aim block;
         * everyone else reads the first. Non-akimbo id 0 is exactly as before. */
        int   gun = (g_akimboOn && id == 1) ? 1 : 0;
        float tx = gun ? g_share->aim2_x : g_share->aim_x;
        float ty = gun ? g_share->aim2_y : g_share->aim_y;
        float *estX = gun ? &g_xhairEst2 : &g_xhairEst;
        float *estY = gun ? &g_xhairEstY2 : &g_xhairEstY;
        DWORD now = GetTickCount();
        int   fresh = 0, ncand = 0;
        long  dxi = 0, dyi = 0;
        int   i;
        float memX = 0, memY = 0;
        int   memOk = xhairFromGame(gun, &memX, &memY);

        /* joysrc=1: the crosshair comes straight from the game's controller
         * block, one per player, so there is nothing to disambiguate - the
         * two akimbo crosshairs cannot swap and a static HUD sprite at
         * priority 0 cannot steal the lock. joysrc=0 is the sprite tracker
         * below, unchanged. */
        if (g_joySrc == 1) {
            if (memOk) { *estX = memX; *estY = memY; fresh = 1; }
            g_xhairX = *estX; g_xhairY = *estY;
        } else
        /* --- pick the real crosshair among the prio-0 candidates ---
         * Track it by nearest to our last lock; if we lose it, re-acquire the
         * candidate nearest the VR target (the gun crosshair is the one being
         * driven toward the target, static HUD sprites sit elsewhere).
         *
         * Limitation (akimbo): with two guns there are two moving crosshairs
         * and this proximity tracker cannot tell which prio-0 sprite is P1's
         * vs P2's - if the two aim points cross, the locks can swap. joysrc=1
         * (xhairFromGame) side-steps that entirely; this path is kept as the
         * fallback and for joysrc=0. Single-gun tracking is unaffected. */
        {
            float bd = 1e18f, bx = 0, by = 0;      /* nearest to current lock  */
            float td = 1e18f, tX = 0, tY = 0;       /* nearest to the anchor    */
            float aX = tx, aY = ty;                 /* where to re-acquire from */
            int   haveB = 0, haveT = 0;
            /* THE ANCHOR IS THE PLAYER'S OWN CROSSHAIR, not the VR target.
             * With two guns the log showed both of them locked on (23,439)
             * while the two controller blocks said the crosshairs were at
             * (20,436) and (616,38) - six hundred pixels apart. The tracker
             * had latched gun 2 onto player 1's sprite on the first frame
             * after P2 joined (only P1's sprites were in the ring yet), and
             * "keep the lock if a candidate is within 200 px" then never let
             * go. Player 2 spent the round driving player 1's crosshair.
             * The controller block cannot be confused this way: there is one
             * per player. Use it to anchor, and to break a lock that has
             * wandered onto somebody else's sprite. */
            if (memOk) {
                float dx = *estX - memX, dy = *estY - memY;
                aX = memX; aY = memY;
                if (dx * dx + dy * dy > 64.0f * 64.0f) { *estX = memX; *estY = memY; }
            }
            for (i = 0; i < XHAIR_CAND; i++) {
                float cx, cy, ex, ey, d;
                if (now - g_candT[i] >= 80) continue;   /* only fresh candidates */
                cx = g_candX[i]; cy = g_candY[i]; ncand++;
                ex = cx - *estX; ey = cy - *estY; d = ex * ex + ey * ey;
                if (d < bd) { bd = d; bx = cx; by = cy; haveB = 1; }
                ex = cx - aX; ey = cy - aY; d = ex * ex + ey * ey;
                if (d < td) { td = d; tX = cx; tY = cy; haveT = 1; }
            }
            if (haveB && bd < 200.0f * 200.0f) {        /* keep the lock */
                *estX = bx; *estY = by; fresh = 1;
            } else if (haveT) {                          /* re-acquire by target */
                *estX = tX; *estY = tY; fresh = 1;
            }
            g_xhairX = *estX; g_xhairY = *estY;   /* for the log */
        }

        if (g_joyMode == 1 && fresh) {                 /* closed loop */
            float ex = (tx - *estX) * g_joyGain;
            float ey = (ty - *estY) * g_joyGain;
            if (g_joyInvertY) ey = -ey;
            dxi = (long)ex; dyi = (long)ey;
            if (dxi > -0x10 && dxi < 0x10) dxi = 0;    /* rest inside dead-zone */
            if (dyi > -0x10 && dyi < 0x10) dyi = 0;
            if (dxi >  127) dxi =  127; if (dxi < -128) dxi = -128;
            if (dyi >  127) dyi =  127; if (dyi < -128) dyi = -128;
            X = 0x8000 + dxi * 256;
            Y = 0x8000 + dyi * 256;
        } else {
            /* NO LIVE CROSSHAIR. That is not an error state, it is the MENU:
             * outside a round [0x004CF1A0+1] is 1, not 2, no crosshair exists
             * and there is nothing to close a loop around.
             *
             * 0x00410C10 says exactly what the menu wants. It takes the
             * unpacked velocities at block +0x20 / +0x22, integrates them into
             * word [0x0045FBD8] / [0x0045FBDC], divides by 0x180 and writes the
             * result as the DIGITAL direction the menu reads. Two things
             * follow, and both were biting:
             *
             *   - a velocity of exactly zero ZEROES the accumulator every frame
             *     (0x00410C8F, 0x00410C9F). joysrc = 1 used to park the axis
             *     dead centre here - "hold, do not drift" - which did not hold
             *     anything, it reset the integrator forever. Hence a menu that
             *     could not be worked at all.
             *
             *   - THOSE TWO ACCUMULATORS ARE ONE PAIR OF GLOBALS, NOT ONE PAIR
             *     PER PLAYER. Both controllers add into the same two words. Let
             *     two guns push at once and the sum crosses +-0x180 on its own:
             *     that is the menu scrolling by itself, and it is the game's
             *     own limitation, not ours. So outside a round only gun 1 gets
             *     an axis; gun 2 is held at centre and cannot fight it.
             *
             * A dead zone around the middle of the screen keeps a hand that is
             * merely near the centre from creeping the cursor. */
            if (gun != 0) {
                X = 0x8000; Y = 0x8000;
            } else {
                /* A menu list is a D-PAD, not a pointer: it steps once per
                 * 0x180 of accumulated velocity and has no position to aim at.
                 * Feeding a velocity PROPORTIONAL to how far off centre the
                 * hand is therefore reads as "nothing happens until you swing
                 * a long way" - the same tilt has to be held far longer near
                 * the dead zone than past it. So it is a dead zone and then a
                 * FIXED rate: past the edge, one step every eight frames,
                 * however far past you are. Small dead zone, brisk repeat. */
                float ex = tx - 320.0f, ey = ty - 240.0f;
                long  step = 0x2F00;               /* ~48 per frame of 0x180 */
                X = 0x8000; Y = 0x8000;
                if (ex < -40.0f) X = 0x8000 - step;
                else if (ex > 40.0f) X = 0x8000 + step;
                if (g_joyInvertY) ey = -ey;
                if (ey < -30.0f) Y = 0x8000 - step;
                else if (ey > 30.0f) Y = 0x8000 + step;
            }
        }

        if (g_joyLog) {
            static DWORD lastLog[2] = { 0, 0 };
            DWORD btnsLog = gun ? g_share->aim2_buttons : g_share->aim_buttons;
            if (now - lastLog[gun] > 100) {
                char b[512], c[160]; DWORD w; HANDLE h;
                DWORD devtype = g_exeBase ? *(DWORD *)EXE_RVA(0x0048F8A0) : 0;
                int   n = 0, cl = 0;
                lastLog[gun] = now;
                /* every fresh prio-0 candidate as tex@x,y - with joysrc=0 this
                 * is what the tracker chose from, with joysrc=1 it is the
                 * cross-check: mem=(..) must sit on the 1360 (P0) / 1344 (P1)
                 * sprite centre */
                c[0] = 0;
                for (i = 0; i < XHAIR_CAND && n < 6; i++) {
                    if (now - g_candT[i] >= 80) continue;
                    cl += wsprintfA(c + cl, " %u@%d,%d", (unsigned)g_candTex[i],
                                    (int)g_candX[i], (int)g_candY[i]);
                    n++;
                    if (cl > 120) break;
                }
                /* in/in2 are the two "this player is in the game" bytes that
                 * 0x0040D300 tests before it draws a crosshair at all
                 * ([0x004CF1A1] and [0x004CF1E5], 2 = playing). If in2 never
                 * reaches 2, akimbo cannot work whatever the aim code does:
                 * player two has not joined and there is no second crosshair
                 * to drive. dev2 is his device type, which must be 4. */
                wsprintfA(b,
                    "t=%u src=%d id=%u dev=%u/%u in=%u/%u cand=%d hits=%d lock=(%d,%d) mem=%d(%d,%d) target=(%d,%d) fed=(%d,%d) btn=%u%s\r\n",
                    now, g_joySrc, id, devtype,
                    (unsigned)(g_exeBase ? *(DWORD *)EXE_RVA(0x0048F8A4) : 0),
                    (unsigned)(g_exeBase ? *(BYTE *)EXE_RVA(0x004CF1A1) : 0),
                    (unsigned)(g_exeBase ? *(BYTE *)EXE_RVA(0x004CF1E5) : 0),
                    ncand, (int)g_xhairHits,
                    (int)*estX, (int)*estY, memOk, (int)memX, (int)memY,
                    (int)tx, (int)ty,
                    (int)dxi, (int)dyi, (unsigned)btnsLog, c);
                g_xhairHits = 0;
                h = CreateFileA("VC2VR_JOY.LOG", FILE_APPEND_DATA, FILE_SHARE_READ,
                                NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
                if (h != INVALID_HANDLE_VALUE) {
                    SetFilePointer(h, 0, NULL, FILE_END);
                    WriteFile(h, b, lstrlenA(b), &w, NULL);
                    CloseHandle(h);
                }
            }
        }
    }
    if (X < 0) X = 0; if (X > 65535) X = 65535;
    if (Y < 0) Y = 0; if (Y > 65535) Y = 65535;

    pji->dwXpos = (DWORD)X;
    pji->dwYpos = (DWORD)Y;
    pji->dwZpos = pji->dwRpos = pji->dwUpos = pji->dwVpos = 0x8000;

    btns_in = (g_akimboOn && id == 1) ? g_share->aim2_buttons
                                      : g_share->aim_buttons;
    {
        DWORD out = 0;
        if ((btns_in & VC2_BTN_FIRE) && !g_fireWas) g_fireTick = GetTickCount();
        g_fireWas = btns_in & VC2_BTN_FIRE;
        if (btns_in & VC2_BTN_FIRE) {
            int fb = (int)g_joyFireBit;             /* fall-back / ini bit */
            if (g_exeBase && id < 4) {              /* prefer the game's own map */
                BYTE gi = *(BYTE *)(EXE_RVA(0x004D4260) + id * 4);  /* gun table */
                BYTE pi = *(BYTE *)(EXE_RVA(0x004D4258) + id * 4);  /* pad table */
                if (gi) fb = gi; else if (pi) fb = pi;
            }
            out |= 1u << (fb & 31);
        }
        if (btns_in & VC2_BTN_START) out |= 1u << (g_joyStartBit & 31);
        if (btns_in & VC2_BTN_BACK)  out |= 1u << (g_joyBackBit  & 31);
        pji->dwButtons = out;
        pji->dwButtonNumber = out ? 1 : 0;
    }
    pji->dwPOV = 0xFFFF;
    return 0;
}

static UINT WINAPI hookJoyGetDevCaps(UINT id, void *pjc, UINT cb)
{
    BYTE *c = (BYTE *)pjc;
    (void)id;
    if (!c || cb < 0x94) return 0;                  /* JOYERR_NOERROR, harmless */
    if (cb > 0x194) cb = 0x194;
    ZeroMemory(c, cb);
    *(WORD *)(c + 0x00) = 0x1234;                    /* wMid */
    *(WORD *)(c + 0x02) = 0x0001;                    /* wPid */
    lstrcpynA((char *)(c + 0x04), "VC2VR Virtual Gun", 32);   /* szPname */
    *(DWORD *)(c + 0x24) = 0;      *(DWORD *)(c + 0x28) = 65535;  /* wX min/max */
    *(DWORD *)(c + 0x2C) = 0;      *(DWORD *)(c + 0x30) = 65535;  /* wY min/max */
    *(DWORD *)(c + 0x34) = 0;      *(DWORD *)(c + 0x38) = 65535;  /* wZ min/max */
    *(DWORD *)(c + 0x3C) = 8;                        /* wNumButtons */
    *(DWORD *)(c + 0x40) = 5;      *(DWORD *)(c + 0x44) = 1000;   /* wPeriod    */
    *(DWORD *)(c + 0x48) = 0;      *(DWORD *)(c + 0x4C) = 65535;  /* wR min/max */
    *(DWORD *)(c + 0x50) = 0;      *(DWORD *)(c + 0x54) = 65535;  /* wU min/max */
    *(DWORD *)(c + 0x58) = 0;      *(DWORD *)(c + 0x5C) = 65535;  /* wV min/max */
    *(DWORD *)(c + 0x60) = 0;                        /* wCaps */
    *(DWORD *)(c + 0x64) = 6;                        /* wMaxAxes */
    *(DWORD *)(c + 0x68) = 2;                        /* wNumAxes */
    *(DWORD *)(c + 0x6C) = 8;                        /* wMaxButtons */
    lstrcpynA((char *)(c + 0x70), "VC2VR", 32);      /* szRegKey */
    if (cb >= 0x94)                                  /* szOEMVxD - NOT segajoy! */
        lstrcpynA((char *)(c + 0x90), "vc2vr.vxd", (int)(cb - 0x90));
    return 0;
}

/* overwrite one IAT slot; save the original. Idempotent across a double load. */
static int joyPatchSlot(DWORD slotVA, void *hook, void **saved)
{
    void **slot = (void **)EXE_RVA(slotVA);
    DWORD old;
    if (IsBadReadPtr(slot, sizeof(void *))) return 0;
    if (*slot == hook) return 1;                     /* already ours */
    if (!VirtualProtect(slot, sizeof(void *), PAGE_READWRITE, &old)) return 0;
    if (saved) *saved = *slot;
    *slot = hook;
    VirtualProtect(slot, sizeof(void *), old, &old);
    return 1;
}

/* the game polls two players unconditionally (0x00426A81 P0, 0x00426A90 P1).
 * Replace the second call with NOPs so player 2 can never join or clutter the
 * screen. Signature: E8 DB BD 00 00  (call 0x00432870 from 0x00426A90). */
static void patchOnePlayer(BYTE *base)
{
    BYTE *p = base + (0x00426A90 - 0x00400000);
    static const BYTE want[5] = { 0xE8, 0xDB, 0xBD, 0x00, 0x00 };
    DWORD old;
    int i;
    /* akimbo needs the game to poll player 2, so never cut it in that mode.
     * (This is set at install time from the ini; the VR side can still decline
     * to drive gun 2 at runtime, that just leaves it centred and idle.) */
    if (!g_onePlayer || g_akimbo || IsBadReadPtr(p, 5)) return;
    if (p[0] == 0x90) return;                        /* already ours */
    for (i = 0; i < 5; i++) if (p[i] != want[i]) return;   /* not the call - bail */
    if (!VirtualProtect(p, 5, PAGE_EXECUTE_READWRITE, &old)) return;
    for (i = 0; i < 5; i++) p[i] = 0x90;
    VirtualProtect(p, 5, old, &old);
    FlushInstructionCache(GetCurrentProcess(), p, 5);
}

static void installJoyHook(BYTE *base)
{
    if (!g_joyGun || g_joyHooked || !base) return;
    g_exeBase = base;
    /* joyGetPosEx IAT = 0x008074A4, joyGetDevCapsA IAT = 0x008074A0 */
    if (joyPatchSlot(0x008074A4, (void *)hookJoyGetPosEx,   (void **)&g_realJoyPos) &&
        joyPatchSlot(0x008074A0, (void *)hookJoyGetDevCaps, (void **)&g_realJoyCaps))
        g_joyHooked = 1;
    if (g_joyForce) *(DWORD *)EXE_RVA(0x0048F8A0) = 3;   /* analog gun, player 0 */
    patchOnePlayer(base);
}

/* --------------------------------------------------------- input injection */
/*
 * Reads the aim block the VR app writes and turns it into input the game can
 * see. Two paths, both driven from here:
 *
 *   mode 1 (default): move the real cursor with SetCursorPos and synthesise
 *   buttons/keys with SendInput. This feeds GetCursorPos, GetAsyncKeyState,
 *   window messages and DirectInput's emulated mouse alike, but only lands in
 *   the game while its window is foreground - which in a headset it is.
 *
 *   mode 2: PostMessage WM_MOUSEMOVE / WM_LBUTTON* / WM_KEY* straight to the
 *   game window. Works without focus, but only if the game reads messages.
 *
 * Everything held down is released when aim_seq stops changing (VR app died)
 * or when the buttons bits drop.
 */

static void injectKey(WORD vk, int down, int mode)
{
    if (mode == 2) {
        if (g_gameWnd)
            PostMessageA(g_gameWnd, down ? WM_KEYDOWN : WM_KEYUP, vk,
                         down ? 1 : (1 | (1u << 30) | (1u << 31)));
        return;
    }
    {
        INPUT in;
        ZeroMemory(&in, sizeof(in));
        in.type = INPUT_KEYBOARD;
        in.ki.wVk = vk;
        in.ki.dwFlags = down ? 0 : KEYEVENTF_KEYUP;
        SendInput(1, &in, sizeof(in));
    }
}

static void injectMouseBtn(int down, int mode, int cx, int cy)
{
    if (mode == 2) {
        if (g_gameWnd)
            PostMessageA(g_gameWnd, down ? WM_LBUTTONDOWN : WM_LBUTTONUP,
                         down ? MK_LBUTTON : 0, MAKELPARAM(cx, cy));
        return;
    }
    {
        INPUT in;
        ZeroMemory(&in, sizeof(in));
        in.type = INPUT_MOUSE;
        in.mi.dwFlags = down ? MOUSEEVENTF_LEFTDOWN : MOUSEEVENTF_LEFTUP;
        SendInput(1, &in, sizeof(in));
    }
}

static DWORD WINAPI aimThread(LPVOID p)
{
    unsigned lastSeq = 0;
    DWORD lastChange = 0;
    unsigned held = 0;                  /* bits we are currently holding down */
    (void)p;

    for (;;) {
        unsigned seq, buttons, want;
        float ax, ay;
        RECT rc;
        POINT tl;
        int cx, cy, cw, ch;
        int foreground;

        Sleep(4);
        if (!g_share || !g_doInject) continue;

        seq = g_share->aim_seq;
        if (seq != lastSeq) { lastSeq = seq; lastChange = GetTickCount(); }

        /* the VR app went quiet: let go of everything and stand down */
        if (GetTickCount() - lastChange > 700) {
            static DWORD lastUnclip;
            DWORD now = GetTickCount();
            if (held & VC2_BTN_FIRE)  injectMouseBtn(0, g_doInject, 0, 0);
            if (held & VC2_BTN_START) injectKey(VK_RETURN, 0, g_doInject);
            if (held & VC2_BTN_BACK)  injectKey(VK_ESCAPE, 0, g_doInject);
            held = 0;
            /* some builds ClipCursor to the window and forget to undo it on
             * pause; while the VR side is silent, keep the desktop usable */
            if (now - lastUnclip > 1000) { ClipCursor(NULL); lastUnclip = now; }
            continue;
        }

        if (!g_gameWnd)
            EnumWindows(findOurWindow, (LPARAM)&g_gameWnd);
        if (!g_gameWnd) continue;

        ax = g_share->aim_x;
        ay = g_share->aim_y;
        buttons = g_share->aim_buttons;

        if (!GetClientRect(g_gameWnd, &rc)) continue;
        cw = rc.right - rc.left;
        ch = rc.bottom - rc.top;
        if (cw < 8 || ch < 8) continue;
        cx = (int)(ax * (float)cw / 640.0f);
        cy = (int)(ay * (float)ch / 480.0f);
        if (cx < 0) cx = 0; if (cx >= cw) cx = cw - 1;
        if (cy < 0) cy = 0; if (cy >= ch) cy = ch - 1;

        foreground = (GetForegroundWindow() == g_gameWnd);

        if (g_doInject == 2) {
            PostMessageA(g_gameWnd, WM_MOUSEMOVE,
                         (buttons & VC2_BTN_FIRE) ? MK_LBUTTON : 0,
                         MAKELPARAM(cx, cy));
        } else if (foreground) {
            tl.x = rc.left; tl.y = rc.top;
            ClientToScreen(g_gameWnd, &tl);
            SetCursorPos(tl.x + cx, tl.y + cy);
        }

        /* edges only; and never press anything into a window that is not
         * foreground in mode 1, or the click lands somewhere else entirely */
        want = buttons;
        if (g_doInject == 1 && !foreground) want = 0;

        if ((want ^ held) & VC2_BTN_FIRE)
            injectMouseBtn(!!(want & VC2_BTN_FIRE), g_doInject, cx, cy);
        if ((want ^ held) & VC2_BTN_START)
            injectKey(VK_RETURN, !!(want & VC2_BTN_START), g_doInject);
        if ((want ^ held) & VC2_BTN_BACK)
            injectKey(VK_ESCAPE, !!(want & VC2_BTN_BACK), g_doInject);
        held = want;
    }
}

/* ----------------------------------------------------------- screen capture */
/*
 * Grabs the game window ~30 times a second and publishes it as 640x480 BGRA.
 * PrintWindow with PW_RENDERFULLCONTENT asks DWM for the composited image, so
 * it works even though dgVoodoo presents through D3D11 and an ordinary BitBlt
 * from the window DC would come back black. Runs in its own thread; the game's
 * render thread never waits for this.
 */

static void learnPath(char *path)
{
    lstrcpyA(path, g_iniPath);
    { int n = lstrlenA(path); while (n > 0 && path[n-1] != '\\') n--; path[n] = 0; }
    lstrcatA(path, "texmap_v6.bin");
}

static void learnSave(void)
{
    char path[MAX_PATH];
    HANDLE f;
    DWORD w, i, cnt = 0;
    LearnRec rec;
    learnPath(path);
    f = CreateFileA(path, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS,
                    FILE_ATTRIBUTE_NORMAL, NULL);
    if (f == INVALID_HANDLE_VALUE) return;
    for (i = 0; i < LEARN_MAX; i++) {
        if (g_learn[i] < 0 || !g_reg[g_learn[i]].used) continue;
        rec.id = i;
        rec.base = g_reg[g_learn[i]].base;
        rec.ord = g_ord[g_learn[i]];
        WriteFile(f, &rec, sizeof(rec), &w, NULL);
        cnt++;
    }
    CloseHandle(f);
    (void)cnt;
}

static void learnLoad(void)
{
    char path[MAX_PATH];
    HANDLE f;
    DWORD r;
    LearnRec rec;
    learnPath(path);
    f = CreateFileA(path, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING,
                    FILE_ATTRIBUTE_NORMAL, NULL);
    if (f == INVALID_HANDLE_VALUE) return;
    while (ReadFile(f, &rec, sizeof(rec), &r, NULL) && r == sizeof(rec))
        if (g_pendingN < LEARN_MAX) g_pending[g_pendingN++] = rec;
    CloseHandle(f);
}

static DWORD WINAPI captureThread(LPVOID p)
{
    HDC winDC = NULL, capDC = NULL, outDC = NULL;
    HBITMAP capBmp = NULL, outBmp = NULL;
    void *outBits = NULL;
    int capW = 0, capH = 0, outW = 0, outH = 0;
    (void)p;

    for (;;) {
        RECT rc;
        int cw, ch, tw, th, ok;

        Sleep(33);
        if (!g_share || !g_doScreen) continue;
        if (!g_gameWnd) {
            EnumWindows(findOurWindow, (LPARAM)&g_gameWnd);
            if (!g_gameWnd) continue;
        }
        if (!GetClientRect(g_gameWnd, &rc)) continue;
        cw = rc.right - rc.left;
        ch = rc.bottom - rc.top;
        if (cw < 8 || ch < 8) continue;

        /* publish at native size when it fits; scale down to fit otherwise.
         * With dgVoodoo forcing a bigger internal resolution the window really
         * carries that detail, and the VR side now takes up to 1280x960. */
        tw = cw; th = ch;
        if (tw > VC2_SCREEN_MAX_W || th > VC2_SCREEN_MAX_H) {
            /* fit preserving aspect, integer math */
            if (tw * VC2_SCREEN_MAX_H > th * VC2_SCREEN_MAX_W) {
                th = th * VC2_SCREEN_MAX_W / tw;
                tw = VC2_SCREEN_MAX_W;
            } else {
                tw = tw * VC2_SCREEN_MAX_H / th;
                th = VC2_SCREEN_MAX_H;
            }
            if (tw < 8) tw = 8;
            if (th < 8) th = 8;
        }

        if (!outDC || outW != tw || outH != th) {
            BITMAPINFO bi;
            HDC screen;
            if (outBmp) { DeleteObject(outBmp); outBmp = NULL; outBits = NULL; }
            if (outDC)  { DeleteDC(outDC); outDC = NULL; }
            ZeroMemory(&bi, sizeof(bi));
            bi.bmiHeader.biSize = sizeof(bi.bmiHeader);
            bi.bmiHeader.biWidth = tw;
            bi.bmiHeader.biHeight = -th;        /* top-down */
            bi.bmiHeader.biPlanes = 1;
            bi.bmiHeader.biBitCount = 32;
            bi.bmiHeader.biCompression = BI_RGB;
            screen = GetDC(NULL);
            outDC = CreateCompatibleDC(screen);
            outBmp = CreateDIBSection(screen, &bi, DIB_RGB_COLORS, &outBits, NULL, 0);
            ReleaseDC(NULL, screen);
            if (!outDC || !outBmp || !outBits) { Sleep(2000); continue; }
            SelectObject(outDC, outBmp);
            SetStretchBltMode(outDC, HALFTONE);
            outW = tw; outH = th;
        }
        if (!capDC || capW != cw || capH != ch) {
            if (capBmp) DeleteObject(capBmp);
            if (capDC) DeleteDC(capDC);
            winDC = GetDC(g_gameWnd);
            capDC = CreateCompatibleDC(winDC);
            capBmp = CreateCompatibleBitmap(winDC, cw, ch);
            ReleaseDC(g_gameWnd, winDC);
            if (!capDC || !capBmp) continue;
            SelectObject(capDC, capBmp);
            capW = cw; capH = ch;
        }

        if (g_capture == 2) {
            /* BitBlt from the desktop DC: DWM composits it, nothing is sent to
             * the game window - PrintWindow made the game repaint its GDI
             * "Loading" splash thirty times a second. Only catch: whatever
             * overlaps the window on the desktop is captured too. */
            POINT tl;
            HDC scr;
            tl.x = rc.left; tl.y = rc.top;
            ClientToScreen(g_gameWnd, &tl);
            scr = GetDC(NULL);
            ok = BitBlt(capDC, 0, 0, cw, ch, scr, tl.x, tl.y, SRCCOPY);
            ReleaseDC(NULL, scr);
        } else {
            ok = PrintWindow(g_gameWnd, capDC, PW_CLIENTONLY | PW_RENDERFULLCONTENT);
        }
        if (ok) {
            if (tw == cw && th == ch)
                ok = BitBlt(outDC, 0, 0, tw, th, capDC, 0, 0, SRCCOPY);
            else
                ok = StretchBlt(outDC, 0, 0, tw, th, capDC, 0, 0, cw, ch, SRCCOPY);
        }

        g_share->screen_seq++;              /* odd: writing */
        _ReadWriteBarrier();
        g_share->screen_ok = ok ? 1u : 0u;
        if (ok) {
            g_share->screen_w = (unsigned)tw;
            g_share->screen_h = (unsigned)th;
            CopyMemory((void *)g_share->screen, outBits, (size_t)tw * th * 4);
            g_share->screen_frame++;
        }
        _ReadWriteBarrier();
        g_share->screen_seq++;              /* even: settled */

        if (g_calib && g_learnCount &&
            GetTickCount() - g_saveAt > 30000) {
            g_saveAt = GetTickCount();
            EnterCriticalSection(&g_lock);
            learnSave();
            LeaveCriticalSection(&g_lock);
        }
        if (ok && g_calib) {
            /* vote: crop this capture at each sizeable quad rectangle and
             * match against the atlas entries of the quad's bank */
            QRect qr[QRECT_MAX];
            int qn, qi, done = 0;
            float sxs = (float)tw / 640.0f, sys = (float)th / 480.0f;
            EnterCriticalSection(&g_lock);
            qn = g_qrDrawN;
            CopyMemory(qr, g_qrDraw, qn * sizeof(QRect));
            LeaveCriticalSection(&g_lock);
            for (qi = 0; qi < qn && done < 48; qi++) {
                QRect *r = &qr[qi];
                int px0 = (int)(r->x0 * sxs), py0 = (int)(r->y0 * sys);
                int px1 = (int)(r->x1 * sxs), py1 = (int)(r->y1 * sys);
                float ph[64], best = 1e9f, second = 1e9f;
                int bi = -1, ri;
                DWORD base;
                if (r->id >= LEARN_MAX) continue;
                if (px0 < 0) px0 = 0;
                if (py0 < 0) py0 = 0;
                if (px1 > tw) px1 = tw;
                if (py1 > th) py1 = th;
                if ((px1 - px0) < 24 || (py1 - py0) < 24) continue;
                done++;
                histOfPixels((const DWORD *)outBits + (SIZE_T)py0 * tw + px0,
                             tw, px1 - px0, py1 - py0, ph);
                /* the quad's bank: largest band base not above the id */
                base = 0;
                {
                    int b2;
                    for (b2 = 0; b2 < BAND_MAX; b2++)
                        if (g_band[b2].live && g_band[b2].base <= r->id &&
                            g_band[b2].base > base) base = g_band[b2].base;
                    if (g_band[0].live && g_band[0].base <= r->id && base == 0)
                        base = g_band[0].base;
                }
                EnterCriticalSection(&g_lock);
                for (ri = 0; ri < g_regCount; ri++) {
                    float d2;
                    if (!g_reg[ri].used || g_reg[ri].base != base) continue;
                    d2 = histDist(ph, g_reg[ri].hist);
                    if (d2 < best) { second = best; best = d2; bi = ri; }
                    else if (d2 < second) second = d2;
                }
                if (bi >= 0 && best < 0.35f && r->sh[0] > 1.0f) {
                    /* light fit: game patch mean / (texture mean * shade) */
                    double pm[3] = { 0, 0, 0 };
                    int cx2, cy2, cn2 = 0, ch2;
                    for (cy2 = py0; cy2 < py1; cy2 += 3)
                        for (cx2 = px0; cx2 < px1; cx2 += 3) {
                            DWORD c = ((const DWORD *)outBits)[(SIZE_T)cy2 * tw + cx2];
                            pm[0] += (c >> 16) & 255;
                            pm[1] += (c >> 8) & 255;
                            pm[2] += c & 255;
                            cn2++;
                        }
                    if (cn2 > 30) {
                        for (ch2 = 0; ch2 < 3; ch2++) {
                            float tm = g_reg[bi].mean[ch2];
                            float k;
                            if (tm < 4.0f) continue;
                            k = (float)(pm[ch2] / cn2) / (tm * r->sh[ch2]);
                            if (k < 0.001f || k > 2.0f) continue;
                            if (g_kFit[ch2] <= 0.0f) g_kFit[ch2] = k;
                            else g_kFit[ch2] = g_kFit[ch2] * 0.98f + k * 0.02f;
                        }
                        InterlockedIncrement(&g_kN);
                    }
                }
                if (bi >= 0 && best < 0.55f && best * 1.35f < second) {
                    Vote *v = g_vote[r->id];
                    int k, hit = -1, freeK = -1;
                    for (k = 0; k < VOTE_K; k++) {
                        if (g_voteN[r->id] > k && v[k].reg == bi) hit = k;
                        else if (freeK < 0 && k >= g_voteN[r->id]) freeK = k;
                    }
                    if (hit >= 0) v[hit].score += 1.0f / (0.05f + best);
                    else if (freeK >= 0) {
                        v[freeK].reg = bi;
                        v[freeK].score = 1.0f / (0.05f + best);
                        g_voteN[r->id]++;
                    }
                    /* promote a clear leader */
                    {
                        float top = 0, run = 0; int tk = -1;
                        for (k = 0; k < g_voteN[r->id]; k++) {
                            if (v[k].score > top) { run = top; top = v[k].score; tk = k; }
                            else if (v[k].score > run) run = v[k].score;
                        }
                        if (tk >= 0 && top > 8.0f && top > run * 2.0f) {
                            if (g_learn[r->id] < 0) g_learnCount++;
                            g_learn[r->id] = v[tk].reg;
                        }
                    }
                }
                LeaveCriticalSection(&g_lock);
            }
        }
    }
}

/* ------------------------------------------------------------ texture dumps */
/*
 * Slot +0x28 is the texture upload: (pixels, palette, table, arg3, count,
 * bank), still only half understood. With texdump = 1 every call is written to
 * texdump\ next to the DLL so the format can be reversed offline without
 * running anything else. Memory is probed page by page - unreadable regions
 * simply truncate the blob instead of crashing the game.
 */

static DWORD dumpBlob(HANDLE f, const void *src, DWORD cap)
{
    const BYTE *b = (const BYTE *)src;
    DWORD done = 0, wrote;
    if (!src) return 0;
    while (done < cap) {
        DWORD chunk = 0x1000 - (((DWORD)(DWORD_PTR)(b + done)) & 0xFFF);
        if (chunk > cap - done) chunk = cap - done;
        if (IsBadReadPtr(b + done, chunk)) break;
        if (!WriteFile(f, b + done, chunk, &wrote, NULL)) break;
        done += chunk;
    }
    return done;
}

/* decode one upload into the atlas and remember where everything landed */
static void texIngest(DWORD a0, DWORD a1, DWORD a2, DWORD a3, DWORD a4)
{
    const BYTE  *pix = (const BYTE *)a0;
    const DWORD *pal = (const DWORD *)a1;
    const DWORD *tab = (const DWORD *)a2;
    DWORD i, off = 0;

    if (!g_atlas || !pix || !pal || !tab || !a4 || a4 > 0x1000) return;
    if (IsBadReadPtr(pal, 1024) || IsBadReadPtr(tab, a4 * 16)) return;

    if (a4 > 400) wcReset();       /* a big upload means a new stage */
    if (g_texCallN < 32) {
        TexCall *tc = &g_texCalls[g_texCallN++];
        DWORD j;
        tc->base = a3; tc->count = a4; tc->d1min = ~0u; tc->d1max = 0;
        for (j = 0; j < a4; j++) {
            DWORD dd = tab[j * 4 + 1];
            if (dd < tc->d1min) tc->d1min = dd;
            if (dd > tc->d1max) tc->d1max = dd;
        }
    }
    {   /* The ids inside this upload now mean other pictures. The sky ring
         * was locked onto tile ids of the previous section and kept drawing
         * them after the train section had reused the slots - an orange
         * gradient across the sky where the panorama had been. Forget every
         * successor link that touches the range and drop the lock; the next
         * frame's own sky tiles re-learn and re-lock. */
        int k, w2 = 0;
        for (k = 0; k < g_succN; k++) {
            if (g_succA[k] - a3 < a4 || g_succB[k] - a3 < a4) continue;
            g_succA[w2] = g_succA[k]; g_succB[w2] = g_succB[k]; w2++;
        }
        g_succN = w2;
        if (g_skyLocked && g_skyLockTex - a3 < a4) {
            g_skyLocked = 0; g_skyHoldOk = 0; g_skyHeld = 0;
        }
    }
    {
        TexBand *b = bandFor(a3);
        if (!b) return;
        for (i = 0; i < a4; i++) {
            DWORD sz = tab[i * 4 + 0];
            int w = (int)(sz & 0xFFFF), h = (int)(sz >> 16);
            int ox, oy, x, y;
            TexReg *r;
            if (w < 1 || h < 1 || w > 2048 || h > 2048) return;  /* lost the plot */
            if (IsBadReadPtr(pix + off, (SIZE_T)w * h)) return;
            r = regSlot(a3 + i);
            {
                /* HGL_D3D 0x10006630 + packer 0x100062B0, read literally:
                 *   dword1 (d1) is a BYTE offset selector: palette + d1*64,
                 *   the pixel index is a full byte into that row (0x10006425),
                 *   dword2 only picks the palette copy size for dynamic
                 *   textures (0x100067D3): 0 -> 1024 bytes, else 64,
                 *   dword3 bit1 = colour key: index 0 becomes the key colour
                 *   (0x100063DD), everything else is opaque - black texels are
                 *   even nudged to (1,0,0) so they cannot hit the key,
                 *   dword3 bit2 = dynamic (own copy, drawn by the sprite slot).
                 * The static path packs the palette low byte into red, so the
                 * palette is stored 0x00BBGGRR (0x10006C61 + 0x10006DB0). */
                DWORD d1 = tab[i * 4 + 1];
                DWORD d3v = tab[i * 4 + 3];
                DWORD dyn = d3v & 4;
                (void)dyn;
                int   keyed = (d3v & 2) != 0;
                const DWORD *palRow = pal + d1 * 16;
                BYTE  maxIdx = 0;
                {   /* bound the palette read by the indices actually used */
                    SIZE_T n = (SIZE_T)w * h, k;
                    const BYTE *p = pix + off;
                    for (k = 0; k < n; k++) if (p[k] > maxIdx) maxIdx = p[k];
                }
                if (IsBadReadPtr(palRow, ((SIZE_T)maxIdx + 1) * 4)) r = NULL;
                if (r && atlasAlloc(b, w, h, &ox, &oy)) {
                for (y = 0; y < h; y++)
                    for (x = 0; x < w; x++) {
                        BYTE idx = pix[off + (SIZE_T)y * w + x];
                        DWORD c, a;
                        c = palRow[idx];
                        /* the packer at 0x10006C61 pulls red out of the LOW
                         * byte, for every texture - dynamic ones included, as
                         * the cyan "PRESS START" proved. */
                        c = ((c & 0xFF) << 16) | (c & 0xFF00) |
                            ((c >> 16) & 0xFF);
                        /* 0x00 = hole by the engine rule, 0x80 = index 0 in
                         * a texture the engine does NOT key (kept opaque, but
                         * [K] can cut it to prove the rule), 0xFF = solid */
                        a = (idx == 0) ? (keyed ? 0u : 0x80000000u)
                                       : 0xFF000000u;
                        g_atlas[(SIZE_T)(oy + y) * VC2_ATLAS_W + ox + x] =
                            a | (c & 0x00FFFFFFu);
                    }
                /* half-texel inset so linear sampling never bleeds neighbours */
                r->u0 = ((float)ox + 0.5f) / VC2_ATLAS_W;
                r->v0 = ((float)oy + 0.5f) / VC2_ATLAS_H;
                r->u1 = ((float)(ox + w) - 0.5f) / VC2_ATLAS_W;
                r->v1 = ((float)(oy + h) - 0.5f) / VC2_ATLAS_H;
                r->key = a3 + i;
                r->d3  = d3v;
                r->base = a3;
                r->used = 1;
                histOfPixels(g_atlas + (SIZE_T)oy * VC2_ATLAS_W + ox,
                             VC2_ATLAS_W, w, h, r->hist);
                {
                    double mr = 0, mg = 0, mb = 0;
                    int cnt = 0, yy2, xx2;
                    for (yy2 = 0; yy2 < h; yy2++)
                        for (xx2 = 0; xx2 < w; xx2++) {
                            DWORD c = g_atlas[(SIZE_T)(oy + yy2) * VC2_ATLAS_W + ox + xx2];
                            if (!(c >> 24)) continue;
                            mr += (c >> 16) & 255;
                            mg += (c >> 8) & 255;
                            mb += c & 255;
                            cnt++;
                        }
                    if (cnt) {
                        r->mean[0] = (float)(mr / cnt);
                        r->mean[1] = (float)(mg / cnt);
                        r->mean[2] = (float)(mb / cnt);
                    } else r->mean[0] = r->mean[1] = r->mean[2] = 1.0f;
                    /* the top row on its own: the sky cap is painted with it,
                     * and the average of the whole panorama would be far too
                     * pale because most of it is cloud */
                    mr = mg = mb = 0; cnt = 0;
                    for (yy2 = 0; yy2 < (h < 4 ? h : 4); yy2++)
                        for (xx2 = 0; xx2 < w; xx2++) {
                            DWORD c = g_atlas[(SIZE_T)(oy + yy2) * VC2_ATLAS_W + ox + xx2];
                            if (!(c >> 24)) continue;
                            mr += (c >> 16) & 255;
                            mg += (c >> 8) & 255;
                            mb += c & 255;
                            cnt++;
                        }
                    if (cnt) {
                        r->top[0] = (float)(mr / cnt);
                        r->top[1] = (float)(mg / cnt);
                        r->top[2] = (float)(mb / cnt);
                    } else { r->top[0] = r->top[1] = r->top[2] = 128.0f; }
                }
                {
                    int bi2, pi2;
                    for (bi2 = 0; bi2 < BAND_MAX; bi2++)
                        if (g_band[bi2].live && g_band[bi2].base == a3) break;
                    if (bi2 < BAND_MAX) {
                        g_ord[(int)(r - g_reg)] = g_ordNext[bi2];
                        for (pi2 = 0; pi2 < g_pendingN; pi2++)
                            if (g_pending[pi2].base == a3 &&
                                g_pending[pi2].ord == g_ordNext[bi2] &&
                                g_pending[pi2].id < LEARN_MAX) {
                                if (g_learn[g_pending[pi2].id] < 0) g_learnCount++;
                                g_learn[g_pending[pi2].id] = (int)(r - g_reg);
                            }
                        g_ordNext[bi2]++;
                    }
                }
                g_atlasDirty = 1;
                InterlockedExchange(&g_pvAtlDirty, 1);
                }
            }
            off += (DWORD)w * h;
        }
    }
}

static void publishAtlas(void)
{
    if (!g_share || !g_atlas || !g_atlasDirty) return;
    g_share->atlas_seq++;               /* odd: writing */
    _ReadWriteBarrier();
    CopyMemory((void *)g_share->atlas, g_atlas,
               (SIZE_T)VC2_ATLAS_W * VC2_ATLAS_H * 4);
    g_share->atlas_frame++;
    _ReadWriteBarrier();
    g_share->atlas_seq++;               /* even: settled */
    g_atlasDirty = 0;
}

static DWORD __stdcall wrap_tex(DWORD a0, DWORD a1, DWORD a2,
                                DWORD a3, DWORD a4, DWORD a5)
{
    if (g_doTex) {
        EnterCriticalSection(&g_lock);
        texIngest(a0, a1, a2, a3, a4);
        publishAtlas();
        LeaveCriticalSection(&g_lock);
    }
    if (g_doTexdump) {
        static LONG n;
        LONG call = InterlockedIncrement(&n);
        char dir[MAX_PATH], path[MAX_PATH];
        HANDLE f;
        lstrcpyA(dir, g_iniPath);
        {   /* g_iniPath ends in HGL_VIEW.ini - cut to the folder */
            int i = lstrlenA(dir);
            while (i > 0 && dir[i - 1] != '\\') i--;
            dir[i] = 0;
        }
        lstrcatA(dir, "texdump");
        CreateDirectoryA(dir, NULL);
        wsprintfA(path, "%s\\call_%03d_bank_%u.bin", dir, call, a5);
        f = CreateFileA(path, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS,
                        FILE_ATTRIBUTE_NORMAL, NULL);
        if (f != INVALID_HANDLE_VALUE) {
            DWORD hdr[16], wrote;
            DWORD capTab = (a4 && a4 < 0x1000) ? a4 * 16 : 0x4000;
            SetFilePointer(f, 64, NULL, FILE_BEGIN);
            {
                DWORD wTab = dumpBlob(f, (void *)a2, capTab);
                DWORD offPal = 64 + wTab;
                DWORD wPal = dumpBlob(f, (void *)a1, 0x400);
                DWORD offPix = offPal + wPal;
                DWORD wPix = dumpBlob(f, (void *)a0, 0x80000);
                hdr[0] = 0x44584554;        /* 'TEXD' */
                hdr[1] = 1;                 /* dump format version */
                hdr[2] = a0; hdr[3] = a1; hdr[4] = a2;
                hdr[5] = a3; hdr[6] = a4; hdr[7] = a5;
                hdr[8] = 64;   hdr[9]  = wTab;      /* table  offset, size */
                hdr[10] = offPal; hdr[11] = wPal;   /* palette */
                hdr[12] = offPix; hdr[13] = wPix;   /* pixels  */
                hdr[14] = hdr[15] = 0;
                SetFilePointer(f, 0, NULL, FILE_BEGIN);
                WriteFile(f, hdr, sizeof(hdr), &wrote, NULL);
            }
            CloseHandle(f);
        }
    }
    return ((DWORD (__stdcall *)(DWORD, DWORD, DWORD, DWORD, DWORD, DWORD))
            g_real[SLOT_TEX])(a0, a1, a2, a3, a4, a5);
}

/* ------------------------------------------------------------------- exports */

static DWORD cfgNum(const char *key, DWORD def)
{
    char b[64];
    if (g_iniPath[0] &&
        GetPrivateProfileStringA("view", key, "", b, sizeof(b), g_iniPath)) {
        DWORD v = 0; int i = 0;
        if (b[0] < '0' || b[0] > '9') return def;
        while (b[i] >= '0' && b[i] <= '9') v = v * 10 + (b[i++] - '0');
        return v;
    }
    return def;
}

/* cfgNum stops at the first character that is not a digit, so a minus sign
 * fell through to the default - and the default was handed back as a DWORD,
 * so groundy = -1030 became 4294966258 and the slab sat four billion units
 * under the road. That is the whole reason the ground fill did nothing. */
static int cfgInt(const char *key, int def)
{
    char b[64];
    if (g_iniPath[0] &&
        GetPrivateProfileStringA("view", key, "", b, sizeof(b), g_iniPath)) {
        int i = 0, sign = 1, v = 0, any = 0;
        while (b[i] == ' ' || b[i] == '\t') i++;
        if (b[i] == '-') { sign = -1; i++; }
        else if (b[i] == '+') i++;
        while (b[i] >= '0' && b[i] <= '9') { v = v * 10 + (b[i++] - '0'); any = 1; }
        if (!any) return def;
        return v * sign;
    }
    return def;
}

/* "1603-1609,1619-1623" -> ranges. Anything that is not a digit, a dash or a
 * separator ends the list, so a comment after the value costs nothing. */
static int cfgRanges(const char *key, IdRange *out, int max)
{
    char b[160];
    int n = 0, i = 0;
    if (!g_iniPath[0] ||
        !GetPrivateProfileStringA("view", key, "", b, sizeof(b), g_iniPath))
        return 0;
    while (b[i] && n < max) {
        unsigned lo = 0, hi;
        int any = 0;
        while (b[i] == ' ' || b[i] == '\t' || b[i] == ',' || b[i] == ';') i++;
        while (b[i] >= '0' && b[i] <= '9') { lo = lo * 10 + (unsigned)(b[i++] - '0'); any = 1; }
        if (!any) break;
        hi = lo;
        if (b[i] == '-') {
            i++;
            hi = 0;
            while (b[i] >= '0' && b[i] <= '9') hi = hi * 10 + (unsigned)(b[i++] - '0');
            if (hi < lo) hi = lo;
        }
        out[n].lo = lo; out[n].hi = hi; n++;
    }
    return n;
}

static BOOL init(void)
{
    char dir[MAX_PATH], path[MAX_PATH];
    int len;
    double fovDeg, half;

    if (g_target) return TRUE;

    GetModuleFileNameA(g_self, dir, sizeof(dir));
    len = lstrlenA(dir);
    while (len > 0 && dir[len - 1] != '\\') len--;
    dir[len] = 0;
    lstrcpyA(g_iniPath, dir);
    lstrcatA(g_iniPath, "HGL_VIEW.ini");

    if (g_iniPath[0])
        GetPrivateProfileStringA("view", "target", "HGL_D3D.DLL",
                                 g_targetName, sizeof(g_targetName), g_iniPath);
    fovDeg = (double)cfgNum("fov", 60);
    if (fovDeg < 5.0 || fovDeg > 170.0) fovDeg = 60.0;
    g_fovDeg = (float)fovDeg;
    g_unitsPerMetre = (float)cfgNum("units_per_metre", 134);
    if (g_unitsPerMetre < 1.0f) g_unitsPerMetre = 134.0f;
    g_doShare  = (int)cfgNum("share", 1);
    /* The preview window was how this was developed before there was a
     * headset to look through. It is still a real D3D11 window, so Windows
     * hands it the foreground the moment it appears - which is why "bring the
     * game to the front" looked broken: the game did come forward, and then
     * the preview took it back. Off by default now. */
    g_doWindow = (int)cfgNum("window", 0);
    g_doInject = (int)cfgNum("inject", 1);
    g_joyGun     = (int)cfgNum("joygun", 1);
    g_joyForce   = (int)cfgNum("joyforce", 1);
    g_akimbo     = (int)cfgNum("akimbo", 0);
    g_joyGain    = (float)cfgInt("joygain", 200) / 100.0f;   /* percent: 200 = 2.00 */
    g_joyMode    = (int)cfgNum("joymode", 1);
    g_joyLog     = (int)cfgNum("joylog", 0);
    g_onePlayer  = (int)cfgNum("oneplayer", 1);
    g_joyFireBit = (LONG)cfgNum("joyfirebit", 0);
    g_joyStartBit= (LONG)cfgNum("joystartbit", 1);
    g_joyBackBit = (LONG)cfgNum("joybackbit", 2);
    g_joyInvertY = (int)cfgNum("joyinverty", 0);
    g_joySrc     = (int)cfgNum("joysrc", 1);
    g_doScreen = (int)cfgNum("screen", 1);
    g_doShade  = (int)cfgNum("shade", 1);
    g_doTexdump = (int)cfgNum("texdump", 0);
    g_doTex    = (int)cfgNum("textures", 1);
    g_texMap   = (int)cfgNum("texmap", 2);   /* kept for the ini, unused now */
    g_alphaKey = (int)cfgNum("alphakey", 1);
    g_uvOrder  = (LONG)cfgNum("uvorder", 0);
    g_texGain  = (LONG)cfgNum("texgain", 250);
    g_capture  = (int)cfgNum("capture", 2);
    {
        int li;
        for (li = 0; li < LEARN_MAX; li++) g_learn[li] = -1;
    }
    learnLoad();
    if (g_doTex) {
        g_atlas = (DWORD *)VirtualAlloc(NULL,
                    (SIZE_T)VC2_ATLAS_W * VC2_ATLAS_H * 4,
                    MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
        if (!g_atlas) g_doTex = 0;
    }

    if (g_doShare) {
        g_shareMap = CreateFileMappingA(INVALID_HANDLE_VALUE, NULL, PAGE_READWRITE,
                                        0, sizeof(Vc2Frame), VC2_SHARE_NAME);
        if (g_shareMap)
            g_share = (Vc2Frame *)MapViewOfFile(g_shareMap, FILE_MAP_ALL_ACCESS,
                                                0, 0, sizeof(Vc2Frame));
        if (g_share) {
            g_share->seq = 0;
            g_share->frame = 0;
            g_share->vertex_count = 0;
        }
    }
    half = fovDeg * 3.14159265358979 / 360.0;
    g_fx = (float)(320.0 / tan(half));
    g_fy = (float)(360.0 / tan(half));
    g_fxIni = g_fx; g_fyIni = g_fy;
    g_projFov = (float)fovDeg;
    g_liveProj = (int)cfgNum("liveproj", 1);
    g_winW = (int)cfgNum("width", 1280);
    g_winH = (int)cfgNum("height", 720);
    g_skip3 = (int)cfgNum("skip3", 0);
    g_zflip = (LONG)cfgNum("zflip", 0);
    g_depthTest = (int)cfgNum("depth", 0);
    g_doSprites = (int)cfgNum("sprites", 1);
    g_sprDist = (float)cfgNum("sprdist", 312);
    g_sprFar = (float)cfgNum("sprfar", 90000);
    g_skyDome = (int)cfgNum("skydome", 1);
    g_skyRep = (int)cfgNum("skyrepeat", 2);
    g_skyCap = (int)cfgNum("skycap", 1);
    g_wcOn = (int)cfgNum("worldcache", 0);
    wcInit();
    g_uvOrder = (LONG)cfgInt("uvorder", -1);
    g_texGain = (LONG)cfgNum("texgain", 100);

    g_noCull = (int)cfgNum("nocull", 1);
    g_noObjCull = (int)cfgNum("noobjcull", 1);
    g_clampDrop = (int)cfgNum("clampdrop", 1);
    g_nearDrop  = (int)cfgNum("neardrop", 1);
    g_deepDrop  = (int)cfgNum("deepdrop", 0);
    g_behindDrop= (int)cfgNum("behinddrop", 0);
    g_nearOwn   = (float)cfgNum("nearown", 800);
    g_texLearn = (int)cfgNum("texlearn", 0);
    g_hudFix = (int)cfgNum("hudfix", 1);
    g_hudSpread = (int)cfgNum("hudspread", 100);
    g_hudScale  = (int)cfgNum("hudscale", 100);
    g_hudHideN  = cfgRanges("hudhide", g_hudHide, IDR_MAX);
    g_panelIdsN = cfgRanges("panelids", g_panelIds, IDR_MAX);
    g_panelDist = cfgInt("paneldist", 110);
    g_panelDrop = cfgInt("paneldrop", 60);
    g_panelScale= cfgInt("panelscale", 100);
    g_hudLog    = cfgInt("hudlog", 0);
    g_hudOwn    = cfgInt("hudown", 0);
    g_hudOwnSize= cfgInt("hudownsize", 100);
    g_hudLives  = cfgInt("hudlives", 0);
    g_skyDebug  = cfgInt("skydebug", 0);
    g_skyHold   = cfgInt("skyhold", 600);
    g_sprMissFar = (int)cfgNum("sprmissfar", 96);
    g_distDebug  = (int)cfgNum("distdebug", 0);
    g_aimProbe   = (int)cfgNum("aimprobe", 0);
    g_farLayers  = cfgNum("farlayers", 0);
    g_farScale   = cfgInt("farscale", 800);
    g_autoFar    = cfgInt("autofar", 1);
    g_afMin      = cfgInt("autofarmin", 15);
    g_afRatio    = cfgInt("autofarratio", 20);
    g_farAuto      = cfgInt("farlayerauto", 1);
    g_farAutoCount = cfgInt("farautocount", 40);
    g_farAutoNear  = cfgInt("farautonear", 12);
    g_nwRadial   = cfgInt("nwradial", 1);
    if (g_hudSpread < 20) g_hudSpread = 20;
    if (g_hudSpread > 400) g_hudSpread = 400;
    if (g_hudScale < 20) g_hudScale = 20;
    if (g_hudScale > 400) g_hudScale = 400;
    g_hideXhair = (int)cfgNum("hidexhair", 1);
    g_pvFollow  = (int)cfgNum("previewfollow", 1);
    g_pvZoom    = (int)cfgNum("previewzoom", 130);
    if (g_pvZoom < 50) g_pvZoom = 50;
    if (g_pvZoom > 400) g_pvZoom = 400;
    g_pvFull    = (int)cfgNum("previewfull", 0);
    g_groundFill = (int)cfgNum("groundfill", 0);
    g_levelWorld = (int)cfgNum("levelworld", 1);
    g_skyLock    = (int)cfgNum("skylock", 1);
    g_groundY = (float)cfgInt("groundy", -215);
    g_groundSize = (float)cfgInt("groundsize", 60000);
    g_groundTex = (LONG)cfgInt("groundtex", -1);
    g_groundTile = (float)cfgInt("groundtile", 8);
    if (g_groundTile < 1.0f) g_groundTile = 1.0f;
    g_trueXyz  = (int)cfgNum("truexyz", 1);
    g_trueClip = (int)cfgNum("trueclip", 1);
    g_splitDepth = (int)cfgNum("splitdepth", 0x20);
    if (g_splitDepth < 2) g_splitDepth = 2;
    if (g_splitDepth > 0x20) g_splitDepth = 0x20;
    if (g_trueClip) g_trueXyz = 1;              /* exact quads need the projector hook */
    g_behindOn = (int)cfgNum("behind", 0);
    if (!g_trueXyz) g_behindOn = 0;
    g_passOn   = (int)cfgNum("passes", 0);
    g_passA    = (int)cfgNum("passa", 0);
    g_passB    = (int)cfgNum("passb", 1);
    g_omCull   = (int)cfgNum("omcull", 1);
    g_omFar    = (int)cfgNum("omfar", 1);
    g_omLocal  = (int)cfgNum("omlocal", 1);
    g_wedgeFix = (int)cfgNum("wedgefix", 1);
    g_wedgeHi  = (int)cfgNum("wedgehi", 600);
    g_nearDropX = (int)cfgNum("neardropx", 1);
    g_skyCull  = (int)cfgNum("skycull", 1);
    g_skyHi    = (int)cfgNum("skyhi", 3000);
    g_skyDist  = (int)cfgNum("skydist", 16000);
    g_noLifeDec = (int)cfgNum("nolifedec", 0);
    lifeDecApply();
    if (g_passOn && !g_excHooked) {
        g_excHooked = 1;
        AddVectoredExceptionHandler(1, passExcHandler);
        passLog("--- session start ---\r\n");
    }
    g_passUpDown = (int)cfgNum("passupdown", 1);
    g_passDedup = (int)cfgNum("passdedup", 1);
    g_passTol = (int)cfgNum("passtol", 3);
    g_passLogVerbose = (int)cfgNum("passlogverbose", 0);
    g_shotLog = (int)cfgNum("shotlog", 0);
    g_skyAmb = (int)cfgNum("skyamb", 0);
    g_splashDepth = (int)cfgNum("splashdepth", 1);
    g_shotTex = (DWORD)cfgNum("shottex", 1344);
    g_shotSpr = (int)cfgNum("shotspr", 1);
    g_cityMemory = (int)cfgNum("citymemory", 1);
    g_cityRadius = (float)cfgNum("cityradius", 15000);
    g_omCap = (int)cfgNum("citymax", 2500);
    g_cityBack = (int)cfgNum("cityback", 0);
    if (g_cityBack < 0) g_cityBack = 0;
    if (g_cityBack > 32) g_cityBack = 32;
    if (g_passOn) g_behindOn = 0;               /* the passes draw what is behind */
    g_quadCap = (int)cfgNum("quadcap", 2900);
    if (g_quadCap > 2990) g_quadCap = 2990;
    g_cityAhead = (int)cfgNum("cityahead", 2);
    if (g_cityAhead < 0) g_cityAhead = 0;
    if (g_cityAhead > 32) g_cityAhead = 32;
    /* The log of session 16's probe run answered every probe with zero -
     * because the run was made with passdedup = 0, which the log itself never
     * said. A run must document the config it actually saw, or a whole
     * session's numbers describe the wrong experiment. */
    {
        char cb[512];
        wsprintfA(cb, "build " __DATE__ " " __TIME__ "\r\n");
        passLog(cb);
        wsprintfA(cb, "cfg passes %d passdedup %d passtol %d passupdown %d "
                      "citymemory %d cityback %d cityahead %d truexyz %d trueclip %d "
                      "neardrop %d clampdrop %d nearown %d ini %s\r\n",
                  g_passOn, g_passDedup, g_passTol, g_passUpDown,
                  g_cityMemory, g_cityBack, g_cityAhead, g_trueXyz, g_trueClip,
                  g_nearDrop, g_clampDrop, (int)g_nearOwn, g_iniPath);
        passLog(cb);
    }
    patchCull();

    lstrcpyA(path, dir);
    lstrcatA(path, g_targetName);
    g_target = LoadLibraryA(path);
    if (!g_target) g_target = LoadLibraryA(g_targetName);
    if (!g_target) return FALSE;
    g_realFunc = (DWORD (__stdcall *)(void **, const char *))
                 GetProcAddress(g_target, "hFunc");
    g_realName = (DWORD (__stdcall *)(void *))GetProcAddress(g_target, "hGetDLLName");
    return g_realFunc && g_realName;
}

__declspec(dllexport) DWORD __stdcall hGetDLLName(void *info)
{
    DWORD r;
    char *name = (char *)info;
    if (!init()) return (DWORD)-1;
    r = g_realName(info);
    if (lstrlenA(name) < 0x100 - 10) lstrcatA(name, " + 3D view");
    return r;
}

__declspec(dllexport) DWORD __stdcall hFunc(void **table, const char *dev)
{
    void *probe[MAX_SLOTS];
    DWORD r, i, count, lo, hi;

    if (!init()) return (DWORD)-1;
    for (i = 0; i < MAX_SLOTS; i++) probe[i] = NULL;
    r = g_realFunc(probe, dev);

    count = 0;
    for (i = 0; i < MAX_SLOTS; i++) if (probe[i]) count = i + 1;
    lo = (DWORD)(DWORD_PTR)g_target;
    hi = lo + 0x1000000;

    for (i = 0; i < count; i++) {
        g_real[i] = probe[i];
        table[i] = probe[i];
        (void)lo; (void)hi;
    }
    if (count > SLOT_SPRITE) {
        table[SLOT_INIT]  = (void *)wrap_init;
        table[SLOT_QUAD]  = (void *)wrap_quad;
        table[SLOT_FLUSH] = (void *)wrap_flush;
        table[SLOT_TEX]   = (void *)wrap_tex;
        table[SLOT_SPRITE] = (void *)wrap_sprite;
        if (count > SLOT_LIGHT) table[SLOT_LIGHT] = (void *)wrap_light;
    }
    /* every other populated slot gets a counting thunk:
     *   inc dword ptr [g_slotCalls[i]]   FF 05 <abs32>
     *   jmp dword ptr [g_real[i]]        FF 25 <abs32>
     * stack untouched, so the unknown calling conventions survive intact */
    if (!g_thunks)
        g_thunks = (BYTE *)VirtualAlloc(NULL, MAX_SLOTS * THUNK_SIZE,
                       MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
    if (g_thunks) {
        for (i = 0; i < count; i++) {
            BYTE *t = g_thunks + i * THUNK_SIZE;
            if (!probe[i]) continue;
            if (i == SLOT_INIT || i == SLOT_QUAD || i == SLOT_SPRITE ||
                i == SLOT_LIGHT ||
                i == SLOT_FLUSH || i == SLOT_TEX) continue;
            t[0] = 0xFF; t[1] = 0x05;
            *(DWORD *)(t + 2) = (DWORD)(DWORD_PTR)&g_slotCalls[i];
            t[6] = 0xFF; t[7] = 0x25;
            *(DWORD *)(t + 8) = (DWORD)(DWORD_PTR)&g_real[i];
            table[i] = t;
        }
    }

    if (!g_ready && g_doWindow) {
        DWORD tid;
        CreateThread(NULL, 0, viewThread, NULL, 0, &tid);
    }
    {
        static LONG started;
        if (!InterlockedExchange(&started, 1) && g_share) {
            DWORD tid;
            if (g_doInject) CreateThread(NULL, 0, aimThread, NULL, 0, &tid);
            if (g_doScreen) CreateThread(NULL, 0, captureThread, NULL, 0, &tid);
        }
    }
    (void)g_thunks; (void)THUNK_SIZE;
    return r;
}

BOOL WINAPI DllMain(HINSTANCE inst, DWORD reason, LPVOID reserved)
{
    (void)reserved;
    if (reason == DLL_PROCESS_ATTACH) {
        g_self = inst;
        InitializeCriticalSection(&g_lock);
        DisableThreadLibraryCalls(inst);
    }
    return TRUE;
}
