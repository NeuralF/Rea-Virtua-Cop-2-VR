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
static float    g_unitsPerMetre = 644.0f;   /* camera sits 1030 units over the road */
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
static float    g_sprDist = 1500.0f;    /* how far the overlay hangs        */
static float    g_sprFar  = 90000.0f;   /* and how far the sky sits behind  */
static int      g_skyDome = 1;          /* wrap the backdrop around the head */
static int      g_skySeg  = 12;         /* segments per tile                 */
static int      g_skyRep  = 2;          /* copies left and right             */
typedef struct { DWORD tex; float x0, y0, x1, y1, sh[3]; } SkyTile;
static DWORD    g_skyTex[16];           /* textures known to be backdrop */
static int      g_skyTexN;
static float    g_skySpan;
static float    g_skySpanA;             /* widest panorama ever seen, radians */
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
static int   g_texLearn;                /* fall back to the colour vote      */
static int   g_clampDrop = 1;
static LONG  g_clampDropped;
#define TOPQ 3
typedef struct { DWORD tex, flags, from; float sx[4], sy[4]; DWORD w[4]; } TopQuad;
static TopQuad g_top[TOPQ];
static float   g_topW[TOPQ];
static float g_wideMax;
static DWORD g_wideTex, g_wideFlags, g_wideFrom, g_quadRa;

static void pushQuad(const DWORD *q)
{
    float px[4], py[4], pz[4];
    DWORD layer, col, key;
    int i, order[6] = { 0, 1, 2, 0, 2, 3 };
    const TexReg *tr = NULL;
    float qu[4], qv[4];
    int sh[3], base[3], vx[4], flat = 0;
    DWORD vcol[4];

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
    if (g_clampDrop) {
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
        if (sxi < g_sxMin) g_sxMin = sxi;
        if (sxi > g_sxMax) g_sxMax = sxi;
        if (syi < g_syMin) g_syMin = syi;
        if (syi > g_syMax) g_syMax = syi;
        unproject(sxi, *(float *)&q[4 + i * 4],
                  q[6 + i * 4], &px[i], &py[i], &pz[i]);
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
    if (g_buildCount / 6 < MAX_QUADS)
        g_quadKey[g_buildCount / 6] = (unsigned __int64)key + 16;
    for (i = 0; i < 6; i++) {
        int k = order[i];
        DWORD wfull = q[6 + k * 4];
        float dn = 1.0f - (float)wfull / 4194304.0f;   /* 16 layers span */
        if (dn < 0.0f) dn = 0.0f;
        if (dn > 1.0f) dn = 1.0f;
        g_build[g_buildCount].x = px[k];
        g_build[g_buildCount].y = py[k];
        g_build[g_buildCount].z = pz[k];
        g_build[g_buildCount].col = (flat || tr) ? vcol[k] : col;
        g_build[g_buildCount].u = qu[k];
        g_build[g_buildCount].v = qv[k];
        g_build[g_buildCount].d = g_zflip ? 1.0f - dn : dn;
        g_buildCount++;
    }
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
    back = (prio == 3);
    /* Priority 3 is "drawn before everything else", not "is the sky". On the
     * driving stage the dashboard panel arrives at priority 3 too - the probe
     * caught it as texture 1546 at y 373..537, entirely BELOW the centre of
     * the screen. Wrapping that onto the sky cylinder is how the backdrop
     * started going mad. The panorama always straddles or sits above the
     * horizon; anything whose top edge is already below it is overlay. */
    if (back && y0 >= g_cy) { back = 0; prio = 2; }
    dist = back ? g_sprFar : g_sprDist;
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
        int world = (prio == 0) || back ||
                    (g_hudFix == 0) ||
                    (g_hudFix == 1 && tr && tr->base != 0);
        float ffx = world ? g_fx : g_fxIni;
        float ffy = world ? g_fy : g_fyIni;
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

    if (!g_skyN) return;
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
    {
        const TexReg *anchor = regFind(g_sky[t].tex);
        float aL, aR, w1, yt, yb;
        int rep, seg, reps;
        if (!anchor) { g_capHave = 0; return; }
        {
            int c, ch[3];
            float sh[3];
            sh[0] = g_sky[t].sh[0] + (float)g_amb[0];
            sh[1] = g_sky[t].sh[2] + (float)g_amb[2];
            sh[2] = g_sky[t].sh[1] + (float)g_amb[1];
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
        aL = (float)atan(((double)g_sky[t].x0 - (double)g_cx) / g_fx);
        aR = (float)atan(((double)g_sky[t].x1 - (double)g_cx) / g_fx);
        w1 = aR - aL;
        if (w1 < 0.02f) { g_capHave = 0; return; }
        yt = (g_cy - g_sky[t].y0) / g_fy * g_sprFar;
        yb = (g_cy - g_sky[t].y1) / g_fy * g_sprFar;
        g_capY = yt;
        g_capCol = 0x40000000u |
                   ((DWORD)(int)anchor->top[2] << 16) |
                   ((DWORD)(int)anchor->top[1] << 8) |
                   (DWORD)(int)anchor->top[0];
        g_capHave = 1;
        reps = (int)(3.1416f / w1) + 2;
        if (reps > 40) reps = 40;
        for (rep = -reps; rep <= reps; rep++) {
            const TexReg *tr = regFind(skyWalk(g_sky[t].tex, rep));
            float base = aL + (float)rep * w1;
            if (!tr) continue;
            for (seg = 0; seg < g_skySeg; seg++) {
                float fa = (float)seg / (float)g_skySeg;
                float fb = (float)(seg + 1) / (float)g_skySeg;
                float ua = tr->u0 + (tr->u1 - tr->u0) * fa;
                float ub = tr->u0 + (tr->u1 - tr->u0) * fb;
                float ta = base + w1 * fa, tb = base + w1 * fb;
                float ca = (float)cos(ta), sa2 = (float)sin(ta);
                float cb = (float)cos(tb), sb2 = (float)sin(tb);
                float px[4], py[4], pz[4], uu[4], vv[4];
                int i, order[6] = { 0, 1, 2, 0, 2, 3 };
                if (g_buildCount + 12 > MAX_QUADS * 6) return;
                px[0] = g_sprFar * sa2; pz[0] = -g_sprFar * ca; py[0] = yt;
                px[1] = g_sprFar * sb2; pz[1] = -g_sprFar * cb; py[1] = yt;
                px[2] = g_sprFar * sb2; pz[2] = -g_sprFar * cb; py[2] = yb;
                px[3] = g_sprFar * sa2; pz[3] = -g_sprFar * ca; py[3] = yb;
                uu[0] = uu[3] = ua; uu[1] = uu[2] = ub;
                vv[0] = vv[1] = tr->v0; vv[2] = vv[3] = tr->v1;
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
                /* The cap is built on the SAME segment edges as the panorama
                 * it sits on. Drawn as its own coarse 32-sided ring it shared
                 * no vertices with the fine one below, and the mismatched
                 * chords let the background through as a thin dark arc across
                 * the sky - the seam. Sharing the edges makes it watertight. */
                if (g_skyCap) {
                    float yz = yt + g_sprFar * 2.0f;
                    if (g_buildCount / 6 < MAX_QUADS)
                        g_quadKey[g_buildCount / 6] = 0xFFFFFFFFFull;
                    px[2] = 0.0f; pz[2] = 0.0f; py[2] = yz;
                    px[3] = 0.0f; pz[3] = 0.0f; py[3] = yz;
                    py[0] = yt; py[1] = yt;
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

    px[0] = -h; pz[0] = -h;
    px[1] =  h; pz[1] = -h;
    px[2] =  h; pz[2] =  h;
    px[3] = -h; pz[3] =  h;
    for (i = 0; i < 4; i++) py[i] = g_groundY;
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

static int      g_cityAhead = 2;        /* how many extra lists per frame     */
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

static void buildMVP(float *out)
{
    float view[16], proj[16], rotY[16], rotX[16], trans[16], tmp[16];
    float fovY = 1.20f;                    /* ~69 degrees, generous on purpose */
    float aspect = (float)g_winW / (float)g_winH;
    float zn = 20.0f, zf = 400000.0f;
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
    g_hwnd = CreateWindowExA(0, "VC2View", "Virtua Cop 2 - 3D preview",
                             WS_OVERLAPPEDWINDOW, CW_USEDEFAULT, CW_USEDEFAULT,
                             r.right - r.left, r.bottom - r.top,
                             NULL, NULL, g_self, NULL);
    if (!g_hwnd) return FALSE;
    ShowWindow(g_hwnd, SW_SHOW);

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
    if ((g_ready || g_doShare) && !IsBadReadPtr(cmd, 0x58)) {
        EnterCriticalSection(&g_lock);
        pushQuad((const DWORD *)cmd);
        LeaveCriticalSection(&g_lock);
    }
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
    g_share->fov_degrees =
        (g_projOk && g_projFov > 5.0f && g_projFov < 170.0f) ? g_projFov
                                                             : g_fovDeg;
    g_share->units_per_metre = g_unitsPerMetre;
    g_share->reserved[0] = n;      /* no translucent tail, ever */
    g_share->reserved[1] = (g_drawL3End < n) ? g_drawL3End : n;
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

static DWORD __stdcall wrap_flush(void *arg)
{
    EnterCriticalSection(&g_lock);
    wcTrackCamera();
    wcEmit();
    g_wcFrame++;
    pushSkyDome();
    pushGround();
    g_skyN = 0;
    g_sxMinS = g_sxMin; g_sxMaxS = g_sxMax;
    g_syMinS = g_syMin; g_syMaxS = g_syMax;
    g_sxMin = g_syMin = 1e9f; g_sxMax = g_syMax = -1e9f;
    /* the engine draws with no z-buffer at all (ZENABLE 0 at 0x10001FFF): it
     * radix sorts the frame by the per quad key and paints from the largest
     * key - the farthest - downwards. Reproduce that order here; equal keys
     * keep their submission order, which is what the radix sort does too. */
    {
        UINT nq = g_buildCount / 6, k;
        if (nq > MAX_QUADS) nq = MAX_QUADS;
        if (nq > 1) {
            for (k = 0; k < nq; k++)
                g_sortKey[k] = ((0xFFFFFFFFFull - g_quadKey[k]) << 20) |
                               (unsigned __int64)(k & 0xFFFFF);
            qsort(g_sortKey, nq, sizeof(g_sortKey[0]), cmp64);
            for (k = 0; k < nq; k++)
                CopyMemory(g_draw + (SIZE_T)k * 6,
                           g_build + (SIZE_T)(g_sortKey[k] & 0xFFFFF) * 6,
                           6 * sizeof(Vtx));
        } else {
            CopyMemory(g_draw, g_build, g_buildCount * sizeof(Vtx));
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
    g_unitsPerMetre = (float)cfgNum("units_per_metre", 644);
    if (g_unitsPerMetre < 1.0f) g_unitsPerMetre = 644.0f;
    g_doShare  = (int)cfgNum("share", 1);
    g_doWindow = (int)cfgNum("window", 1);
    g_doInject = (int)cfgNum("inject", 1);
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
    g_sprDist = (float)cfgNum("sprdist", 1500);
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
    g_texLearn = (int)cfgNum("texlearn", 0);
    g_hudFix = (int)cfgNum("hudfix", 1);
    g_groundFill = (int)cfgNum("groundfill", 0);
    g_groundY = (float)cfgInt("groundy", -215);
    g_groundSize = (float)cfgInt("groundsize", 60000);
    g_groundTex = (LONG)cfgInt("groundtex", -1);
    g_groundTile = (float)cfgInt("groundtile", 8);
    if (g_groundTile < 1.0f) g_groundTile = 1.0f;
    g_quadCap = (int)cfgNum("quadcap", 2900);
    if (g_quadCap > 2990) g_quadCap = 2990;
    g_cityAhead = (int)cfgNum("cityahead", 2);
    if (g_cityAhead < 0) g_cityAhead = 0;
    if (g_cityAhead > 32) g_cityAhead = 32;
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
