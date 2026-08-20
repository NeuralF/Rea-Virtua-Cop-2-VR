/*
 * VC2VR.exe - renders Virtua Cop 2 in a headset.
 *
 * The game is a 32-bit program from 1997 and SteamVR is 64-bit, so they run
 * apart. HGL_VIEW.DLL, loaded inside the game, turns each frame's screen-space
 * quads back into 3D and publishes them to shared memory. This program reads
 * that and draws it, once per eye, through OpenXR.
 *
 * Controllers (headset mode):
 *      trigger            shoot (left mouse button in the game)
 *      A / X              Start / confirm (Enter)
 *      B / Y              back (Escape)
 *      thumbstick click   floating screen: auto -> always on -> off
 *      grip (squeeze)     recentre on the current head pose
 *
 * The controller is the light gun: its ray is cast against the actual level
 * geometry, the hit point is projected through the game's own camera, and the
 * resulting 640x480 coordinate goes to HGL_VIEW.DLL over shared memory, which
 * moves the real mouse. A red laser and a hit marker are drawn in the world.
 *
 * The floating screen shows a live capture of the game window. It appears by
 * itself whenever the 3D scene is nearly empty - menus, scores, name entry -
 * because those are 2D sprites that never reach the quad slot and would
 * otherwise leave the headset in a void. Point at the screen and the ray maps
 * straight onto it, so the native menus are clicked exactly like with a mouse.
 *
 * Two modes:
 *      VC2VR.exe              headset (default)
 *      VC2VR.exe --window     ordinary window, for checking the pipe alone
 *
 * --window exists so that a failure can be pinned down. If the window shows the
 * scene but the headset does not, the problem is OpenXR; if neither shows it,
 * the problem is the handoff or the game side.
 *
 * Needs openxr_loader.dll beside the executable. It ships with the OpenXR SDK
 * release from Khronos and is not something SteamVR provides.
 */

#define COBJMACROS
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <d3d11.h>
#include <dxgi1_2.h>
#include <d3dcompiler.h>
#include <math.h>
#include <stdio.h>

#define XR_USE_PLATFORM_WIN32
#define XR_USE_GRAPHICS_API_D3D11
#include "openxr/openxr.h"
#include "openxr/openxr_platform.h"

#include "vc2_share.h"

#define NEAR_M 0.05f
#define FAR_M  4000.0f

static void die(const char *what)
{
    printf("\n[fail] %s\n", what);
    printf("press enter to close\n");
    getchar();
    ExitProcess(1);
}

static void note(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    vprintf(fmt, ap);
    va_end(ap);
    fflush(stdout);
}

/* ------------------------------------------------------------------ matrices */
/* stored row-major as m[row * 4 + col]; the shader does mul(m, vector) */

static void mIdent(float *m)
{
    int i;
    for (i = 0; i < 16; i++) m[i] = 0.0f;
    m[0] = m[5] = m[10] = m[15] = 1.0f;
}

static void mMul(const float *a, const float *b, float *o)
{
    float t[16];
    int r, c, k;
    for (r = 0; r < 4; r++)
        for (c = 0; c < 4; c++) {
            float s = 0.0f;
            for (k = 0; k < 4; k++) s += a[r * 4 + k] * b[k * 4 + c];
            t[r * 4 + c] = s;
        }
    for (r = 0; r < 16; r++) o[r] = t[r];
}

/* right handed, looking down -Z, depth 0..1 - what both OpenXR and D3D want */
static void mProjFov(float aL, float aR, float aU, float aD, float zn, float zf, float *m)
{
    float tl = tanf(aL), tr = tanf(aR), tu = tanf(aU), td = tanf(aD);
    float w = tr - tl, h = tu - td;
    mIdent(m);
    m[0] = 2.0f / w;  m[2]  = (tr + tl) / w;
    m[5] = 2.0f / h;  m[6]  = (tu + td) / h;
    /* reversed depth: near maps to 1, far to 0. With a float depth buffer this
     * spends the precision where it matters and stops distant walls flickering. */
    m[10] = zn / (zf - zn);
    m[11] = zf * zn / (zf - zn);
    m[14] = -1.0f;
    m[15] = 0.0f;
}

static void mFromQuat(const XrQuaternionf *q, float *m)
{
    float x = q->x, y = q->y, z = q->z, w = q->w;
    mIdent(m);
    m[0]  = 1 - 2 * (y * y + z * z); m[1] = 2 * (x * y - z * w);     m[2]  = 2 * (x * z + y * w);
    m[4]  = 2 * (x * y + z * w);     m[5] = 1 - 2 * (x * x + z * z); m[6]  = 2 * (y * z - x * w);
    m[8]  = 2 * (x * z - y * w);     m[9] = 2 * (y * z + x * w);     m[10] = 1 - 2 * (x * x + y * y);
}

/* view matrix from a head pose: undo the rotation, then undo the translation */
static void mView(const XrPosef *p, float *out)
{
    float r[16], rt[16], t[16];
    int i, j;
    mFromQuat(&p->orientation, r);
    mIdent(rt);
    for (i = 0; i < 3; i++)
        for (j = 0; j < 3; j++) rt[i * 4 + j] = r[j * 4 + i];
    mIdent(t);
    t[3] = -p->position.x; t[7] = -p->position.y; t[11] = -p->position.z;
    mMul(rt, t, out);
}

/* ---------------------------------------------------------------- shared mem */

static HANDLE    g_map;
static Vc2Frame *g_frame;
static Vc2Vertex g_local[VC2_MAX_VERTS];
static unsigned  g_localCount;
static unsigned  g_lastFrame;
static float     g_unitsPerMetre = 644.0f;
static float     g_gfx = 554.3f, g_gfy = 623.6f;   /* the game's projection */
static float     g_gcx = 320.0f, g_gcy = 240.0f;   /* and its centre        */
static int       g_projLive;        /* projection read out of the game itself */
static float     g_aimSX = 320.0f, g_aimSY = 240.0f;   /* last aim we pushed */
static void hideCrosshair(void);

static unsigned  g_addStart;            /* first translucent vertex        */
static unsigned  g_l3End;               /* end of the background layer     */
static unsigned  g_scrPix[VC2_SCREEN_MAX_W * VC2_SCREEN_MAX_H];
static unsigned  g_atlPix[VC2_ATLAS_W * VC2_ATLAS_H];
static unsigned  g_atlSeqSeen;
static int       g_atlFresh;
static unsigned  g_scrW = 640, g_scrH = 480;    /* size of the last capture */

/* VC2VR.ini next to the exe */
static int g_cfgDepth;
static int g_cfgMsaa = 4;         /* 1 / 2 / 4 / 8 */
static int g_cfgSuper = 140;      /* eye buffer scale in percent */
static int g_cfgZoomX = 250;      /* zoom magnification in percent (250 = 2.5x) */
static int g_cfgZoomSpd = 4;      /* zoom glide, percent of the gap per frame */
static int g_cfgReach = 6;        /* metres to the aim point when the ray misses */
static int g_cfgHideCross = 48;   /* hide the game's crosshair sprite within this
                                   * many pixels of our own aim; 0 keeps it */
static int g_cfgAutoZoom = 1;     /* follow the game's own camera zoom */
static int g_cfgFocus = 1;        /* pull the game window to the front on start */

static void loadCfg(void)
{
    char path[MAX_PATH];
    DWORD n = GetModuleFileNameA(NULL, path, MAX_PATH);
    while (n > 0 && path[n - 1] != '\\') n--;
    lstrcpyA(path + n, "VC2VR.ini");
    g_cfgMsaa  = (int)GetPrivateProfileIntA("vr", "msaa", 4, path);
    g_cfgDepth = (int)GetPrivateProfileIntA("vr", "depth", 0, path);
    g_cfgSuper = (int)GetPrivateProfileIntA("vr", "supersample", 140, path);
    g_cfgZoomX   = (int)GetPrivateProfileIntA("vr", "zoom", 250, path);
    g_cfgZoomSpd = (int)GetPrivateProfileIntA("vr", "zoomspeed", 4, path);
    g_cfgReach   = (int)GetPrivateProfileIntA("vr", "aimreach", 6, path);
    g_cfgHideCross = (int)GetPrivateProfileIntA("vr", "hidecross", 48, path);
    g_cfgAutoZoom  = (int)GetPrivateProfileIntA("vr", "autozoom", 1, path);
    g_cfgFocus     = (int)GetPrivateProfileIntA("vr", "focusgame", 1, path);
    if (g_cfgHideCross > 200) g_cfgHideCross = 200;
    if (g_cfgReach < 1)   g_cfgReach = 1;
    if (g_cfgReach > 100) g_cfgReach = 100;
    if (g_cfgZoomX < 110) g_cfgZoomX = 110;
    if (g_cfgZoomX > 500) g_cfgZoomX = 500;
    if (g_cfgZoomSpd < 1)  g_cfgZoomSpd = 1;
    if (g_cfgZoomSpd > 50) g_cfgZoomSpd = 50;
    if (g_cfgMsaa < 1) g_cfgMsaa = 1;
    if (g_cfgMsaa > 8) g_cfgMsaa = 8;
    if (g_cfgSuper < 50)  g_cfgSuper = 50;
    if (g_cfgSuper > 250) g_cfgSuper = 250;
}
static unsigned  g_scrSeqSeen;
static int       g_scrFresh;        /* new pixels waiting to be uploaded */
static int       g_scrHave;         /* capture is alive at all */

static int openShare(void)
{
    g_map = OpenFileMappingA(FILE_MAP_ALL_ACCESS, FALSE, VC2_SHARE_NAME);
    if (!g_map) return 0;
    g_frame = (Vc2Frame *)MapViewOfFile(g_map, FILE_MAP_ALL_ACCESS, 0, 0, sizeof(Vc2Frame));
    if (g_frame && g_frame->magic == VC2_SHARE_MAGIC &&
        g_frame->version != VC2_SHARE_VERSION)
        note("warning: the game side speaks protocol v%u, this build speaks v%u -\n"
             "         update HGL_VIEW.DLL and VC2VR.exe together\n",
             g_frame->version, (unsigned)VC2_SHARE_VERSION);
    return g_frame != NULL;
}

/* seqlock read: copy, then check nothing moved underneath us */
static int pullFrame(void)
{
    unsigned a, b, n, i;
    if (!g_frame) return 0;
    for (i = 0; i < 8; i++) {
        a = g_frame->seq;
        if (a & 1u) continue;
        MemoryBarrier();
        if (g_frame->magic != VC2_SHARE_MAGIC) return 0;
        n = g_frame->vertex_count;
        if (n > VC2_MAX_VERTS) n = VC2_MAX_VERTS;
        g_addStart = g_frame->reserved[0];
        g_l3End = g_frame->reserved[1];
        CopyMemory(g_local, g_frame->verts, n * sizeof(Vc2Vertex));
        if (g_frame->units_per_metre > 1.0f) g_unitsPerMetre = g_frame->units_per_metre;
        if (!g_projLive &&
            g_frame->fov_degrees > 5.0f && g_frame->fov_degrees < 170.0f) {
            double half = g_frame->fov_degrees * 3.14159265358979 / 360.0;
            g_gfx = (float)(320.0 / tan(half));
            g_gfy = 1.125f * g_gfx;
        }
        MemoryBarrier();
        b = g_frame->seq;
        if (a == b) {
            g_localCount = n;
            g_lastFrame = g_frame->frame;
            hideCrosshair();
            return 1;
        }
    }
    return 0;
}

/* The game keeps drawing its own blue crosshair sprite, and it is redundant
 * next to the laser - worse, it trails the laser by the servo loop's few
 * frames. The DLL cannot be told to drop it (the sprite path is shared with
 * the rest of the HUD), but it is easy to recognise here: a small overlay
 * quad (depth exactly 1.0) whose centre reprojects to where we last told the
 * game to aim - the game moves it there for us. Collapse it to a point.
 * The size gate keeps the ammo drum and the hearts alive when the player
 * happens to aim across a corner of the screen. */
static void hideCrosshair(void)
{
    unsigned i;
    if (!g_cfgHideCross) return;
    for (i = 0; i + 5 < g_localCount; i += 6) {
        Vc2Vertex *q = &g_local[i];
        float cx3, cy3, cz3, ex, ey, px, py, dx, dy;
        float x0 = 1e30f, x1 = -1e30f, y0 = 1e30f, y1 = -1e30f;
        int k, over = 1;
        for (k = 0; k < 6; k++) {
            if (q[k].depth != 1.0f) { over = 0; break; }
            if (q[k].x < x0) x0 = q[k].x;
            if (q[k].x > x1) x1 = q[k].x;
            if (q[k].y < y0) y0 = q[k].y;
            if (q[k].y > y1) y1 = q[k].y;
        }
        if (!over) continue;
        ex = x1 - x0; ey = y1 - y0;
        if (ex > 300.0f || ey > 300.0f) continue;      /* bigger than a sight */
        cx3 = (x0 + x1) * 0.5f;
        cy3 = (y0 + y1) * 0.5f;
        cz3 = -(q[0].z);                               /* overlay: flat in z */
        if (cz3 < 1.0f) continue;
        px = g_gcx + cx3 * g_gfx / cz3;
        py = g_gcy - cy3 * g_gfy / cz3;
        dx = px - g_aimSX; dy = py - g_aimSY;
        if (dx * dx + dy * dy > (float)(g_cfgHideCross * g_cfgHideCross))
            continue;
        for (k = 1; k < 6; k++) q[k] = q[0];           /* zero area, invisible */
    }
}

/* same idea for the captured game screen; a torn frame is retried next time */
static void pullScreen(void)
{
    unsigned a, b;
    if (!g_frame) return;
    a = g_frame->screen_seq;
    if ((a & 1u) || a == g_scrSeqSeen) return;
    MemoryBarrier();
    if (!g_frame->screen_ok) { g_scrSeqSeen = a; return; }
    {
        unsigned w = g_frame->screen_w, h = g_frame->screen_h;
        if (w < 8 || h < 8 || w > VC2_SCREEN_MAX_W || h > VC2_SCREEN_MAX_H) {
            g_scrSeqSeen = a;
            return;
        }
        CopyMemory(g_scrPix, (const void *)g_frame->screen, (size_t)w * h * 4);
        MemoryBarrier();
        b = g_frame->screen_seq;
        if (a == b) {
            g_scrW = w;
            g_scrH = h;
            g_scrSeqSeen = a;
            g_scrFresh = 1;
            g_scrHave = 1;
        }
    }
}

static void pullAtlas(void)
{
    unsigned a, b;
    if (!g_frame) return;
    a = g_frame->atlas_seq;
    if ((a & 1u) || a == g_atlSeqSeen) return;
    MemoryBarrier();
    CopyMemory(g_atlPix, (const void *)g_frame->atlas, sizeof(g_atlPix));
    MemoryBarrier();
    b = g_frame->atlas_seq;
    if (a == b) {
        g_atlSeqSeen = a;
        g_atlFresh = 1;
    }
}

/* ------------------------------------------- the game's live projection
 *
 * The DLL unprojects every quad with the projection the game is using RIGHT
 * NOW - fx/fy at 0x004CF23C/0x004CF238 and the centre at 0x004CF80A/0x004CF808,
 * all rebuilt by the game at runtime (the zoom walks the fov from 60 down to
 * ~18 degrees). The aim maths here must be the EXACT inverse of that
 * unprojection, or the game's crosshair and the laser drift apart - a fixed
 * 60-degree focal length is wrong by 3x at full zoom, and a centre that is
 * not really (320,240) shifts every shot by a constant.
 *
 * fov_degrees in shared memory is the ini value, not the live one, so read
 * the four values straight out of the game process instead: PE base 0x400000,
 * no ASLR, and a 64-bit process reads a 32-bit one without ceremony. */
#include <tlhelp32.h>

static HANDLE g_gameProc;
static DWORD  g_gamePid;
static DWORD  g_gameFindAt;             /* next tick worth retrying at */
static float  g_gfxBase;                /* smallest live fx seen = "no zoom" */

/* The game pauses itself the moment its window loses focus, and the launch
 * ritual was: start the game, start this, alt-tab back to the game. Do the
 * last step ourselves: this process was just started by the user, so it holds
 * the foreground right and is allowed to hand it over. */
static BOOL CALLBACK focusEnum(HWND h, LPARAM lp)
{
    DWORD pid = 0;
    GetWindowThreadProcessId(h, &pid);
    if (pid != (DWORD)lp || !IsWindowVisible(h) || GetWindow(h, GW_OWNER))
        return TRUE;
    ShowWindow(h, SW_RESTORE);
    SetForegroundWindow(h);
    return FALSE;
}

static void gameProcFind(void)
{
    HANDLE snap;
    PROCESSENTRY32 pe;
    DWORD now = GetTickCount();
    if (g_gameProc || (g_gameFindAt && now < g_gameFindAt)) return;
    g_gameFindAt = now + 2000;
    snap = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (snap == INVALID_HANDLE_VALUE) return;
    ZeroMemory(&pe, sizeof(pe));
    pe.dwSize = sizeof(pe);
    if (Process32First(snap, &pe)) do {
        char up[16]; int i;
        for (i = 0; i < 15 && pe.szExeFile[i]; i++)
            up[i] = (char)((pe.szExeFile[i] >= 'a' && pe.szExeFile[i] <= 'z')
                           ? pe.szExeFile[i] - 32 : pe.szExeFile[i]);
        up[i] = 0;
        if (up[0]=='P'&&up[1]=='P'&&up[2]=='J'&&up[3]=='2'&&up[4]=='D'&&up[5]=='D') {
            g_gameProc = OpenProcess(PROCESS_VM_READ, FALSE, pe.th32ProcessID);
            if (g_gameProc) {
                g_gamePid = pe.th32ProcessID;
                note("reading the live projection from %s\n", pe.szExeFile);
                if (g_cfgFocus) EnumWindows(focusEnum, (LPARAM)g_gamePid);
                break;
            }
        }
    } while (Process32Next(snap, &pe));
    CloseHandle(snap);
}

/* one read per frame; on any failure fall back to the fov_degrees estimate
 * and go looking for the process again */
static void gameProjRead(void)
{
    float f[2];                         /* [0]=fy @ 0x4CF238, [1]=fx @ 0x4CF23C */
    short c[2];                         /* [0]=cy @ 0x4CF808, [1]=cx @ 0x4CF80A */
    SIZE_T got;
    gameProcFind();
    if (!g_gameProc) return;
    if (!ReadProcessMemory(g_gameProc, (LPCVOID)(ULONG_PTR)0x004CF238u, f, 8, &got) || got != 8 ||
        !ReadProcessMemory(g_gameProc, (LPCVOID)(ULONG_PTR)0x004CF808u, c, 4, &got) || got != 4) {
        CloseHandle(g_gameProc);
        g_gameProc = NULL;              /* the game went away; retry later */
        g_projLive = 0;
        return;
    }
    /* nonsense means the game has not set them up yet - keep what we have */
    if (!(f[1] > 10.0f && f[1] < 200000.0f) || !(f[0] > 10.0f && f[0] < 200000.0f)) return;
    if (c[1] < 1 || c[1] > 4096 || c[0] < 1 || c[0] > 4096) return;
    g_gfx = f[1]; g_gfy = f[0];
    g_gcx = (float)c[1]; g_gcy = (float)c[0];
    g_projLive = 1;
    /* the smallest fx the game has used is its unzoomed baseline (about 554
     * at 60 degrees); anything above it is the game zooming its own camera */
    if (g_gfxBase < 300.0f || (g_gfx > 300.0f && g_gfx < g_gfxBase))
        g_gfxBase = g_gfx;
}

/* aim result, VR -> game, single writer so a bare bump after the write is fine */
static void pushAim(float sx, float sy, unsigned buttons)
{
    if (!g_frame) return;
    g_aimSX = sx; g_aimSY = sy;
    g_frame->aim_x = sx;
    g_frame->aim_y = sy;
    g_frame->aim_buttons = buttons;
    MemoryBarrier();
    g_frame->aim_seq++;
}

/* --------------------------------------------------------------------- D3D11 */

static ID3D11Device        *g_dev;
static ID3D11DeviceContext *g_ctx;
static ID3D11Buffer        *g_vb, *g_cb;
static ID3D11VertexShader  *g_vs;
static ID3D11PixelShader   *g_ps;
static ID3D11InputLayout   *g_il;
static ID3D11RasterizerState *g_rs;
static ID3D11DepthStencilState *g_dss;
static ID3D11DepthStencilState *g_dssUI;    /* no depth: laser and screen */

/* overlay: laser beam and hit marker, plain coloured triangles, local space */
#define OVERLAY_MAX 64
static ID3D11Buffer *g_ovVB;
static Vc2Vertex     g_ovVerts[OVERLAY_MAX];
static unsigned      g_ovCount;

/* the floating screen: textured quad, local space */
typedef struct { float x, y, z, u, v; } TexVtx;
static ID3D11Buffer            *g_scrVB;
static ID3D11VertexShader      *g_vsTex;
static ID3D11PixelShader       *g_psTex;
static ID3D11InputLayout       *g_ilTex;
static ID3D11Texture2D         *g_scrTex;
static ID3D11ShaderResourceView *g_scrSRV;
static ID3D11SamplerState      *g_samp;
static ID3D11Buffer            *g_cbRes;
static ID3D11BlendState        *g_blendAdd;
static ID3D11Texture2D          *g_atlTex;
static ID3D11ShaderResourceView *g_atlSRV;

/* where the screen hangs, recomputed on every recentre */
static float g_scrC[3]  = { 0, 0, -2.0f };  /* centre       */
static float g_scrR[3]  = { 1, 0, 0 };      /* right        */
static float g_scrU[3]  = { 0, 1, 0 };      /* up           */
static float g_scrN[3]  = { 0, 0, 1 };      /* towards user */
static float g_scrHalfW = 1.0f;             /* 4:3 -> 2.0 x 1.5 m at 2 m */
static float g_scrHalfH = 0.75f;
static int   g_scrMode;                     /* 0 auto, 1 on, 2 off */
static int   g_scrVisible;

/* one shader for the world and the overlay: u < 0 means "no texture, colour
 * as-is"; textured vertices carry the game's shading in the colour with 0x80
 * neutral, hence the * 2. clip() gives cutout transparency without blending,
 * so draw order does not matter against the depth buffer. */
static const char *SRC =
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

/* Sharp bilinear: snap sample positions to texel centres, but blend across
 * exactly one destination pixel at each texel seam. Pixel art stays crisp on
 * the two-metre screen without the shimmer of plain nearest sampling. */
static const char *SRC_TEX =
"cbuffer C : register(b0) { row_major float4x4 mvp; };\n"
"cbuffer R : register(b1) { float2 res; float2 pad; };\n"
"Texture2D tex : register(t0); SamplerState smp : register(s0);\n"
"struct VIn  { float3 p : POSITION; float2 t : TEXCOORD; };\n"
"struct VOut { float4 p : SV_POSITION; float2 t : TEXCOORD; };\n"
"VOut vs(VIn i) { VOut o; o.p = mul(mvp, float4(i.p,1)); o.t = i.t; return o; }\n"
"float4 ps(VOut i) : SV_TARGET {\n"
"    float2 pix = i.t * res - 0.5;\n"
"    float2 c   = floor(pix);\n"
"    float2 f   = pix - c;\n"
"    float2 w   = clamp(fwidth(pix), 1e-5, 1.0);\n"
"    f = clamp((f - 0.5) / w, -0.5, 0.5) + 0.5;\n"
"    return float4(tex.Sample(smp, (c + 0.5 + f) / res).rgb, 1);\n"
"}\n";

static void makePipeline(void)
{
    ID3DBlob *vsb = NULL, *psb = NULL, *err = NULL;
    D3D11_INPUT_ELEMENT_DESC ie[4];
    D3D11_BUFFER_DESC bd;
    D3D11_RASTERIZER_DESC rd;
    D3D11_DEPTH_STENCIL_DESC dd;

    if (FAILED(D3DCompile(SRC, lstrlenA(SRC), NULL, NULL, NULL, "vs", "vs_4_0", 0, 0, &vsb, &err)))
        die("vertex shader would not compile");
    if (FAILED(D3DCompile(SRC, lstrlenA(SRC), NULL, NULL, NULL, "ps", "ps_4_0", 0, 0, &psb, &err)))
        die("pixel shader would not compile");
    ID3D11Device_CreateVertexShader(g_dev, ID3D10Blob_GetBufferPointer(vsb),
                                    ID3D10Blob_GetBufferSize(vsb), NULL, &g_vs);
    ID3D11Device_CreatePixelShader(g_dev, ID3D10Blob_GetBufferPointer(psb),
                                   ID3D10Blob_GetBufferSize(psb), NULL, &g_ps);

    ZeroMemory(ie, sizeof(ie));
    ie[0].SemanticName = "POSITION"; ie[0].Format = DXGI_FORMAT_R32G32B32_FLOAT;
    ie[1].SemanticName = "COLOR";    ie[1].Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    ie[1].AlignedByteOffset = 12;
    ie[2].SemanticName = "TEXCOORD"; ie[2].Format = DXGI_FORMAT_R32G32_FLOAT;
    ie[2].AlignedByteOffset = 16;
    ie[3].SemanticName = "TEXCOORD"; ie[3].SemanticIndex = 1;
    ie[3].Format = DXGI_FORMAT_R32_FLOAT;
    ie[3].AlignedByteOffset = 24;
    ID3D11Device_CreateInputLayout(g_dev, ie, 4, ID3D10Blob_GetBufferPointer(vsb),
                                   ID3D10Blob_GetBufferSize(vsb), &g_il);
    ID3D10Blob_Release(vsb); ID3D10Blob_Release(psb);

    ZeroMemory(&bd, sizeof(bd));
    bd.ByteWidth = VC2_MAX_VERTS * sizeof(Vc2Vertex);
    bd.Usage = D3D11_USAGE_DYNAMIC;
    bd.BindFlags = D3D11_BIND_VERTEX_BUFFER;
    bd.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
    if (FAILED(ID3D11Device_CreateBuffer(g_dev, &bd, NULL, &g_vb))) die("vertex buffer");

    ZeroMemory(&bd, sizeof(bd));
    bd.ByteWidth = 64;
    bd.Usage = D3D11_USAGE_DYNAMIC;
    bd.BindFlags = D3D11_BIND_CONSTANT_BUFFER;
    bd.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
    if (FAILED(ID3D11Device_CreateBuffer(g_dev, &bd, NULL, &g_cb))) die("constant buffer");

    ZeroMemory(&rd, sizeof(rd));
    rd.FillMode = D3D11_FILL_SOLID;
    rd.CullMode = D3D11_CULL_NONE;      /* winding order is not known, draw both faces */
    ID3D11Device_CreateRasterizerState(g_dev, &rd, &g_rs);

    ZeroMemory(&dd, sizeof(dd));
    /* the game has no z-buffer (HGL_D3D sets ZENABLE 0): the DLL hands the
     * quads over already sorted back to front, so painting in order is the
     * faithful thing to do. depth=1 in VC2VR.ini brings the buffer back. */
    dd.DepthEnable = g_cfgDepth ? TRUE : FALSE;
    dd.DepthWriteMask = g_cfgDepth ? D3D11_DEPTH_WRITE_MASK_ALL
                                   : D3D11_DEPTH_WRITE_MASK_ZERO;
    dd.DepthFunc = D3D11_COMPARISON_GREATER;
    ID3D11Device_CreateDepthStencilState(g_dev, &dd, &g_dss);

    dd.DepthEnable = FALSE;
    dd.DepthWriteMask = D3D11_DEPTH_WRITE_MASK_ZERO;
    ID3D11Device_CreateDepthStencilState(g_dev, &dd, &g_dssUI);

    /* --- textured pipeline for the floating screen --- */
    if (FAILED(D3DCompile(SRC_TEX, lstrlenA(SRC_TEX), NULL, NULL, NULL, "vs", "vs_4_0", 0, 0, &vsb, &err)))
        die("textured vertex shader would not compile");
    if (FAILED(D3DCompile(SRC_TEX, lstrlenA(SRC_TEX), NULL, NULL, NULL, "ps", "ps_4_0", 0, 0, &psb, &err)))
        die("textured pixel shader would not compile");
    ID3D11Device_CreateVertexShader(g_dev, ID3D10Blob_GetBufferPointer(vsb),
                                    ID3D10Blob_GetBufferSize(vsb), NULL, &g_vsTex);
    ID3D11Device_CreatePixelShader(g_dev, ID3D10Blob_GetBufferPointer(psb),
                                   ID3D10Blob_GetBufferSize(psb), NULL, &g_psTex);
    ZeroMemory(ie, sizeof(ie));
    ie[0].SemanticName = "POSITION"; ie[0].Format = DXGI_FORMAT_R32G32B32_FLOAT;
    ie[1].SemanticName = "TEXCOORD"; ie[1].Format = DXGI_FORMAT_R32G32_FLOAT;
    ie[1].AlignedByteOffset = 12;
    ID3D11Device_CreateInputLayout(g_dev, ie, 2, ID3D10Blob_GetBufferPointer(vsb),
                                   ID3D10Blob_GetBufferSize(vsb), &g_ilTex);
    ID3D10Blob_Release(vsb); ID3D10Blob_Release(psb);

    ZeroMemory(&bd, sizeof(bd));
    bd.ByteWidth = OVERLAY_MAX * sizeof(Vc2Vertex);
    bd.Usage = D3D11_USAGE_DYNAMIC;
    bd.BindFlags = D3D11_BIND_VERTEX_BUFFER;
    bd.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
    if (FAILED(ID3D11Device_CreateBuffer(g_dev, &bd, NULL, &g_ovVB))) die("overlay buffer");

    bd.ByteWidth = 6 * sizeof(TexVtx);
    if (FAILED(ID3D11Device_CreateBuffer(g_dev, &bd, NULL, &g_scrVB))) die("screen buffer");

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
        ID3D11Device_CreateBlendState(g_dev, &bld, &g_blendAdd);
    }
    bd.ByteWidth = 16;                    /* cbuffer R: screen resolution */
    bd.BindFlags = D3D11_BIND_CONSTANT_BUFFER;
    if (FAILED(ID3D11Device_CreateBuffer(g_dev, &bd, NULL, &g_cbRes))) die("res cbuffer");

    {
        D3D11_SAMPLER_DESC sdd;
        ZeroMemory(&sdd, sizeof(sdd));
        sdd.Filter = D3D11_FILTER_MIN_MAG_MIP_LINEAR;
        sdd.AddressU = sdd.AddressV = sdd.AddressW = D3D11_TEXTURE_ADDRESS_CLAMP;
        ID3D11Device_CreateSamplerState(g_dev, &sdd, &g_samp);
    }
    {
        D3D11_TEXTURE2D_DESC td;
        ZeroMemory(&td, sizeof(td));
        td.Width = VC2_ATLAS_W; td.Height = VC2_ATLAS_H;
        td.MipLevels = 1; td.ArraySize = 1;
        td.Format = DXGI_FORMAT_B8G8R8A8_UNORM;
        td.SampleDesc.Count = 1;
        td.Usage = D3D11_USAGE_DYNAMIC;
        td.BindFlags = D3D11_BIND_SHADER_RESOURCE;
        td.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
        if (FAILED(ID3D11Device_CreateTexture2D(g_dev, &td, NULL, &g_atlTex))) die("atlas texture");
        ID3D11Device_CreateShaderResourceView(g_dev, (ID3D11Resource *)g_atlTex, NULL, &g_atlSRV);
    }
    /* the screen texture itself is (re)made on demand - its size follows the
     * capture, see ensureScreenTex */
}

static void uploadAtlasTex(void)
{
    D3D11_MAPPED_SUBRESOURCE m;
    unsigned y;
    if (!g_atlFresh || !g_atlTex) return;
    if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_atlTex, 0,
                  D3D11_MAP_WRITE_DISCARD, 0, &m))) {
        for (y = 0; y < VC2_ATLAS_H; y++)
            CopyMemory((BYTE *)m.pData + y * m.RowPitch,
                       g_atlPix + (size_t)y * VC2_ATLAS_W, VC2_ATLAS_W * 4);
        ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_atlTex, 0);
    }
    g_atlFresh = 0;
}

/* recreate the capture texture whenever the incoming size changes */
static void ensureScreenTex(void)
{
    D3D11_TEXTURE2D_DESC td;
    static unsigned haveW, haveH;
    if (g_scrTex && haveW == g_scrW && haveH == g_scrH) return;
    if (g_scrSRV) { ID3D11ShaderResourceView_Release(g_scrSRV); g_scrSRV = NULL; }
    if (g_scrTex) { ID3D11Texture2D_Release(g_scrTex); g_scrTex = NULL; }
    ZeroMemory(&td, sizeof(td));
    td.Width = g_scrW; td.Height = g_scrH;
    td.MipLevels = 1; td.ArraySize = 1;
    td.Format = DXGI_FORMAT_B8G8R8A8_UNORM;       /* GDI hands out BGRA */
    td.SampleDesc.Count = 1;
    td.Usage = D3D11_USAGE_DYNAMIC;
    td.BindFlags = D3D11_BIND_SHADER_RESOURCE;
    td.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
    if (FAILED(ID3D11Device_CreateTexture2D(g_dev, &td, NULL, &g_scrTex))) return;
    ID3D11Device_CreateShaderResourceView(g_dev, (ID3D11Resource *)g_scrTex, NULL, &g_scrSRV);
    haveW = g_scrW; haveH = g_scrH;
}

/* ------------------------------------------------------- little vector math */

static float vDot(const float *a, const float *b)
{ return a[0]*b[0] + a[1]*b[1] + a[2]*b[2]; }

static void vCross(const float *a, const float *b, float *o)
{
    float t0 = a[1]*b[2] - a[2]*b[1];
    float t1 = a[2]*b[0] - a[0]*b[2];
    float t2 = a[0]*b[1] - a[1]*b[0];
    o[0] = t0; o[1] = t1; o[2] = t2;
}

static void vNorm(float *a)
{
    float l = sqrtf(vDot(a, a));
    if (l > 1e-9f) { a[0] /= l; a[1] /= l; a[2] /= l; }
}

static void quatRotate(const XrQuaternionf *q, const float *v, float *o)
{
    /* o = v + 2*cross(q.xyz, cross(q.xyz, v) + q.w*v) */
    float u[3] = { q->x, q->y, q->z };
    float t[3], t2[3];
    vCross(u, v, t);
    t[0] += q->w * v[0]; t[1] += q->w * v[1]; t[2] += q->w * v[2];
    vCross(u, t, t2);
    o[0] = v[0] + 2.0f * t2[0];
    o[1] = v[1] + 2.0f * t2[1];
    o[2] = v[2] + 2.0f * t2[2];
}

/* Moeller-Trumbore, nearest hit over the frame's triangles, game units */
static int rayVsScene(const float *org, const float *dir, float *tOut)
{
    unsigned i;
    float best = 1e30f;
    int found = 0;
    for (i = 0; i + 2 < g_localCount; i += 3) {
        float e1[3], e2[3], p[3], tv[3], qv[3];
        float det, inv, u, v, t;
        const Vc2Vertex *a = &g_local[i], *b = &g_local[i+1], *c = &g_local[i+2];
        /* The overlay - the game's own crosshair, the ammo drum, the hearts -
         * hangs 2.3 m in front of the camera (d exactly 1.0), and the sky
         * panorama sits behind everything (d exactly 0.0). Neither is a thing
         * a light gun shoots AT: casting against the crosshair quad makes the
         * aim chase its own tail, which is precisely the "crosshair living its
         * own life" symptom. World geometry carries the engine's depth key,
         * strictly between the two. */
        if ((a->depth == 1.0f && b->depth == 1.0f && c->depth == 1.0f) ||
            (a->depth == 0.0f && b->depth == 0.0f && c->depth == 0.0f))
            continue;
        e1[0] = b->x - a->x; e1[1] = b->y - a->y; e1[2] = b->z - a->z;
        e2[0] = c->x - a->x; e2[1] = c->y - a->y; e2[2] = c->z - a->z;
        vCross(dir, e2, p);
        det = vDot(e1, p);
        if (det > -1e-6f && det < 1e-6f) continue;
        inv = 1.0f / det;
        tv[0] = org[0] - a->x; tv[1] = org[1] - a->y; tv[2] = org[2] - a->z;
        u = vDot(tv, p) * inv;
        if (u < 0.0f || u > 1.0f) continue;
        vCross(tv, e1, qv);
        v = vDot(dir, qv) * inv;
        if (v < 0.0f || u + v > 1.0f) continue;
        t = vDot(e2, qv) * inv;
        if (t > 1.0f && t < best) { best = t; found = 1; }
    }
    if (found) *tOut = best;
    return found;
}

/* a thin beam as two crossed ribbons, so it is visible from every side */
static void ovBeam(const float *a, const float *b, float halfWidth, DWORD col)
{
    float d[3] = { b[0]-a[0], b[1]-a[1], b[2]-a[2] };
    float up[3] = { 0, 1, 0 }, s1[3], s2[3];
    int r, k;
    vCross(d, up, s1);
    if (vDot(s1, s1) < 1e-12f) { s1[0] = 1; s1[1] = 0; s1[2] = 0; }
    vNorm(s1);
    vCross(d, s1, s2);
    vNorm(s2);
    for (r = 0; r < 2; r++) {
        const float *s = r ? s2 : s1;
        float q[4][3];
        static const int idx[6] = { 0, 1, 2, 0, 2, 3 };
        for (k = 0; k < 3; k++) {
            q[0][k] = a[k] - s[k]*halfWidth;
            q[1][k] = a[k] + s[k]*halfWidth;
            q[2][k] = b[k] + s[k]*halfWidth;
            q[3][k] = b[k] - s[k]*halfWidth;
        }
        for (k = 0; k < 6; k++) {
            if (g_ovCount >= OVERLAY_MAX) return;
            g_ovVerts[g_ovCount].x = q[idx[k]][0];
            g_ovVerts[g_ovCount].y = q[idx[k]][1];
            g_ovVerts[g_ovCount].z = q[idx[k]][2];
            g_ovVerts[g_ovCount].colour = col;
            g_ovVerts[g_ovCount].u = -1.0f;
            g_ovVerts[g_ovCount].v = -1.0f;
            g_ovVerts[g_ovCount].depth = 1.0f;
            g_ovCount++;
        }
    }
}

static void uploadVerts(void)
{
    D3D11_MAPPED_SUBRESOURCE m;
    if (!g_localCount) return;
    if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_vb, 0,
                  D3D11_MAP_WRITE_DISCARD, 0, &m))) {
        CopyMemory(m.pData, g_local, g_localCount * sizeof(Vc2Vertex));
        ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_vb, 0);
    }
}

/* Side by side needs two viewports in one back buffer, and only the second eye
 * must not wipe the first. g_vpX is where this eye starts, g_noClear says the
 * buffer has already been cleared this frame. Both are zero everywhere else,
 * so the headset path is byte for byte what it was. */
static float g_vpX;
static int   g_noClear;

static void drawWith(ID3D11RenderTargetView *rtv, ID3D11DepthStencilView *dsv,
                     int w, int h, const float *mvp)
{
    float clear[4] = { 0.02f, 0.02f, 0.03f, 1.0f };
    D3D11_MAPPED_SUBRESOURCE m;
    D3D11_VIEWPORT vp;
    UINT stride = sizeof(Vc2Vertex), offset = 0;

    if (!g_noClear) {
        ID3D11DeviceContext_ClearRenderTargetView(g_ctx, rtv, clear);
        ID3D11DeviceContext_ClearDepthStencilView(g_ctx, dsv, D3D11_CLEAR_DEPTH, 0.0f, 0);
    }
    ID3D11DeviceContext_OMSetRenderTargets(g_ctx, 1, &rtv, dsv);
    ID3D11DeviceContext_OMSetDepthStencilState(g_ctx, g_dss, 0);

    ZeroMemory(&vp, sizeof(vp));
    vp.TopLeftX = g_vpX;
    vp.Width = (float)w; vp.Height = (float)h; vp.MaxDepth = 1.0f;
    ID3D11DeviceContext_RSSetViewports(g_ctx, 1, &vp);
    ID3D11DeviceContext_RSSetState(g_ctx, g_rs);

    if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_cb, 0,
                  D3D11_MAP_WRITE_DISCARD, 0, &m))) {
        CopyMemory(m.pData, mvp, 64);
        ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_cb, 0);
    }

    ID3D11DeviceContext_IASetInputLayout(g_ctx, g_il);
    ID3D11DeviceContext_IASetPrimitiveTopology(g_ctx, D3D11_PRIMITIVE_TOPOLOGY_TRIANGLELIST);
    ID3D11DeviceContext_IASetVertexBuffers(g_ctx, 0, 1, &g_vb, &stride, &offset);
    ID3D11DeviceContext_VSSetShader(g_ctx, g_vs, NULL, 0);
    ID3D11DeviceContext_VSSetConstantBuffers(g_ctx, 0, 1, &g_cb);
    ID3D11DeviceContext_PSSetShader(g_ctx, g_ps, NULL, 0);
    ID3D11DeviceContext_PSSetShaderResources(g_ctx, 0, 1, &g_atlSRV);
    ID3D11DeviceContext_PSSetSamplers(g_ctx, 0, 1, &g_samp);
    if (g_localCount) ID3D11DeviceContext_Draw(g_ctx, g_localCount, 0);
}

/* hang the screen in front of a pose: 2 m out, 4:3, facing back at it */
static void setScreenPose(float x, float y, float z, float yaw)
{
    float fwd[3] = { -sinf(yaw), 0.0f, -cosf(yaw) };
    D3D11_MAPPED_SUBRESOURCE m;
    TexVtx v[6];
    int i;
    static const float corner[6][2] = {
        { -1,  1 }, { 1, 1 }, { 1, -1 },
        { -1,  1 }, { 1, -1 }, { -1, -1 } };

    g_scrR[0] = cosf(yaw); g_scrR[1] = 0; g_scrR[2] = -sinf(yaw);
    g_scrU[0] = 0; g_scrU[1] = 1; g_scrU[2] = 0;
    g_scrN[0] = -fwd[0]; g_scrN[1] = 0; g_scrN[2] = -fwd[2];
    g_scrC[0] = x + fwd[0] * 2.0f;
    g_scrC[1] = y;
    g_scrC[2] = z + fwd[2] * 2.0f;

    if (!g_scrVB) return;
    for (i = 0; i < 6; i++) {
        float cu = corner[i][0], cv = corner[i][1];
        v[i].x = g_scrC[0] + g_scrR[0]*cu*g_scrHalfW + g_scrU[0]*cv*g_scrHalfH;
        v[i].y = g_scrC[1] + g_scrR[1]*cu*g_scrHalfW + g_scrU[1]*cv*g_scrHalfH;
        v[i].z = g_scrC[2] + g_scrR[2]*cu*g_scrHalfW + g_scrU[2]*cv*g_scrHalfH;
        v[i].u = (cu + 1.0f) * 0.5f;
        v[i].v = (1.0f - cv) * 0.5f;
    }
    if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_scrVB, 0,
                  D3D11_MAP_WRITE_DISCARD, 0, &m))) {
        CopyMemory(m.pData, v, sizeof(v));
        ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_scrVB, 0);
    }
}

static void uploadScreenTex(void)
{
    D3D11_MAPPED_SUBRESOURCE m;
    unsigned y;
    if (!g_scrFresh) return;
    ensureScreenTex();
    if (!g_scrTex) return;
    if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_scrTex, 0,
                  D3D11_MAP_WRITE_DISCARD, 0, &m))) {
        for (y = 0; y < g_scrH; y++)
            CopyMemory((BYTE *)m.pData + y * m.RowPitch,
                       g_scrPix + y * g_scrW, g_scrW * 4);
        ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_scrTex, 0);
    }
    if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_cbRes, 0,
                  D3D11_MAP_WRITE_DISCARD, 0, &m))) {
        float r[4];
        r[0] = (float)g_scrW; r[1] = (float)g_scrH; r[2] = r[3] = 0.0f;
        CopyMemory(m.pData, r, sizeof(r));
        ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_cbRes, 0);
    }
    g_scrFresh = 0;
}

static void uploadOverlay(void)
{
    D3D11_MAPPED_SUBRESOURCE m;
    if (!g_ovCount) return;
    if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_ovVB, 0,
                  D3D11_MAP_WRITE_DISCARD, 0, &m))) {
        CopyMemory(m.pData, g_ovVerts, g_ovCount * sizeof(Vc2Vertex));
        ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_ovVB, 0);
    }
}

/* laser, hit marker and the floating screen; call right after drawWith, with
 * view * proj only - all of it lives in local (metre) space, not game space */
static void drawUI(const float *vp)
{
    D3D11_MAPPED_SUBRESOURCE m;
    UINT stride, offset = 0;

    if (SUCCEEDED(ID3D11DeviceContext_Map(g_ctx, (ID3D11Resource *)g_cb, 0,
                  D3D11_MAP_WRITE_DISCARD, 0, &m))) {
        CopyMemory(m.pData, vp, 64);
        ID3D11DeviceContext_Unmap(g_ctx, (ID3D11Resource *)g_cb, 0);
    }
    ID3D11DeviceContext_OMSetDepthStencilState(g_ctx, g_dssUI, 0);

    if (g_scrVisible && g_scrHave && g_scrSRV) {
        stride = sizeof(TexVtx);
        ID3D11DeviceContext_IASetInputLayout(g_ctx, g_ilTex);
        ID3D11DeviceContext_IASetVertexBuffers(g_ctx, 0, 1, &g_scrVB, &stride, &offset);
        ID3D11DeviceContext_VSSetShader(g_ctx, g_vsTex, NULL, 0);
        ID3D11DeviceContext_PSSetShader(g_ctx, g_psTex, NULL, 0);
        ID3D11DeviceContext_PSSetConstantBuffers(g_ctx, 1, 1, &g_cbRes);
        ID3D11DeviceContext_PSSetShaderResources(g_ctx, 0, 1, &g_scrSRV);
        ID3D11DeviceContext_PSSetSamplers(g_ctx, 0, 1, &g_samp);
        ID3D11DeviceContext_Draw(g_ctx, 6, 0);
    }
    if (g_ovCount) {
        stride = sizeof(Vc2Vertex);
        ID3D11DeviceContext_IASetInputLayout(g_ctx, g_il);
        ID3D11DeviceContext_IASetVertexBuffers(g_ctx, 0, 1, &g_ovVB, &stride, &offset);
        ID3D11DeviceContext_VSSetShader(g_ctx, g_vs, NULL, 0);
        ID3D11DeviceContext_PSSetShader(g_ctx, g_ps, NULL, 0);
        ID3D11DeviceContext_Draw(g_ctx, g_ovCount, 0);
    }
}

/* ------------------------------------------------------------------- OpenXR */

static PFN_xrGetInstanceProcAddr xrGIPA;
#define XRFN(name) static PFN_##name p##name
XRFN(xrCreateInstance); XRFN(xrDestroyInstance); XRFN(xrGetSystem);
XRFN(xrGetSystemProperties); XRFN(xrCreateSession); XRFN(xrDestroySession);
XRFN(xrCreateReferenceSpace); XRFN(xrEnumerateViewConfigurationViews);
XRFN(xrCreateSwapchain); XRFN(xrEnumerateSwapchainImages);
XRFN(xrEnumerateSwapchainFormats);
XRFN(xrAcquireSwapchainImage); XRFN(xrWaitSwapchainImage); XRFN(xrReleaseSwapchainImage);
XRFN(xrBeginSession); XRFN(xrEndSession); XRFN(xrWaitFrame); XRFN(xrBeginFrame);
XRFN(xrEndFrame); XRFN(xrLocateViews); XRFN(xrPollEvent); XRFN(xrResultToString);
XRFN(xrEnumerateInstanceExtensionProperties);
XRFN(xrStringToPath); XRFN(xrCreateActionSet); XRFN(xrCreateAction);
XRFN(xrCreateActionSpace); XRFN(xrSuggestInteractionProfileBindings);
XRFN(xrAttachSessionActionSets); XRFN(xrSyncActions);
XRFN(xrGetActionStateBoolean); XRFN(xrGetActionStateFloat); XRFN(xrLocateSpace);
#undef XRFN

/* the loader can only name results once an instance exists, and the failures
 * that matter most happen before that, so keep a small table of our own */
static const char *xrName(XrResult r)
{
    switch ((int)r) {
    case  0: return "XR_SUCCESS";
    case -1: return "XR_ERROR_VALIDATION_FAILURE";
    case -2: return "XR_ERROR_RUNTIME_FAILURE";
    case -3: return "XR_ERROR_OUT_OF_MEMORY";
    case -4: return "XR_ERROR_API_VERSION_UNSUPPORTED (runtime is older than we asked for)";
    case -6: return "XR_ERROR_INITIALIZATION_FAILED (runtime present but would not start)";
    case -7: return "XR_ERROR_FUNCTION_UNSUPPORTED";
    case -8: return "XR_ERROR_FEATURE_UNSUPPORTED";
    case -9: return "XR_ERROR_EXTENSION_NOT_PRESENT";
    case -13: return "XR_ERROR_HANDLE_INVALID";
    case -50: return "XR_ERROR_FORM_FACTOR_UNSUPPORTED";
    case -51: return "XR_ERROR_FORM_FACTOR_UNAVAILABLE (no headset - enable the null driver)";
    default: return "unknown XrResult";
    }
}

static void loadXr(XrInstance inst)
{
#define GET(n) do { if (XR_FAILED(xrGIPA(inst, #n, (PFN_xrVoidFunction *)&p##n))) \
                        die("missing OpenXR entry point " #n); } while (0)
    GET(xrGetSystem); GET(xrGetSystemProperties); GET(xrCreateSession);
    GET(xrDestroySession); GET(xrCreateReferenceSpace);
    GET(xrEnumerateViewConfigurationViews); GET(xrCreateSwapchain);
    GET(xrEnumerateSwapchainImages); GET(xrEnumerateSwapchainFormats);
    GET(xrAcquireSwapchainImage); GET(xrWaitSwapchainImage);
    GET(xrReleaseSwapchainImage); GET(xrBeginSession); GET(xrEndSession);
    GET(xrWaitFrame); GET(xrBeginFrame); GET(xrEndFrame); GET(xrLocateViews);
    GET(xrPollEvent); GET(xrDestroyInstance); GET(xrResultToString);
    GET(xrStringToPath); GET(xrCreateActionSet); GET(xrCreateAction);
    GET(xrCreateActionSpace); GET(xrSuggestInteractionProfileBindings);
    GET(xrAttachSessionActionSets); GET(xrSyncActions);
    GET(xrGetActionStateBoolean); GET(xrGetActionStateFloat); GET(xrLocateSpace);
#undef GET
}

/* ------------------------------------------------------ controller actions */

static XrActionSet g_actSet;
static XrAction    g_actAim, g_actFire, g_actStart, g_actBack, g_actToggle, g_actGrip, g_actZoom;
static volatile float g_zoomLevel = 1.0f;   /* 1 = no zoom; held stick raises it */
static XrPath      g_handPath[2];               /* 0 = left, 1 = right */
static XrSpace     g_aimSpace[2];
static int         g_activeHand = 1;            /* the light-gun hand */

static XrPath path(XrInstance inst, const char *s)
{
    XrPath p = XR_NULL_PATH;
    pxrStringToPath(inst, s, &p);
    return p;
}

/* one profile's worth of suggested bindings; a refusal is fine, some runtimes
 * simply do not know a given controller */
static void suggest(XrInstance inst, const char *profile,
                    const XrActionSuggestedBinding *b, uint32_t n)
{
    XrInteractionProfileSuggestedBinding s;
    XrResult r;
    ZeroMemory(&s, sizeof(s));
    s.type = XR_TYPE_INTERACTION_PROFILE_SUGGESTED_BINDING;
    s.interactionProfile = path(inst, profile);
    s.suggestedBindings = b;
    s.countSuggestedBindings = n;
    r = pxrSuggestInteractionProfileBindings(inst, &s);
    if (XR_FAILED(r)) note("  bindings for %s not accepted (%d), skipped\n", profile, (int)r);
}

#define BIND(act, p) do { bb[bn].action = (act); bb[bn].binding = path(inst, p); bn++; } while (0)

static void initActions(XrInstance inst, XrSession session)
{
    XrActionSetCreateInfo asci;
    XrActionCreateInfo aci;
    XrSessionActionSetsAttachInfo at;
    XrActionSuggestedBinding bb[24];
    uint32_t bn;
    int h;

    g_handPath[0] = path(inst, "/user/hand/left");
    g_handPath[1] = path(inst, "/user/hand/right");

    ZeroMemory(&asci, sizeof(asci));
    asci.type = XR_TYPE_ACTION_SET_CREATE_INFO;
    lstrcpyA(asci.actionSetName, "gameplay");
    lstrcpyA(asci.localizedActionSetName, "Gameplay");
    if (XR_FAILED(pxrCreateActionSet(inst, &asci, &g_actSet)))
        die("could not create the action set");

#define MAKE(var, name, loc, kind) do {                                   \
        ZeroMemory(&aci, sizeof(aci));                                    \
        aci.type = XR_TYPE_ACTION_CREATE_INFO;                            \
        lstrcpyA(aci.actionName, name);                                   \
        lstrcpyA(aci.localizedActionName, loc);                           \
        aci.actionType = kind;                                            \
        aci.countSubactionPaths = 2;                                      \
        aci.subactionPaths = g_handPath;                                  \
        if (XR_FAILED(pxrCreateAction(g_actSet, &aci, &var)))             \
            die("could not create action " name);                         \
    } while (0)

    MAKE(g_actAim,    "aim",    "Aim",             XR_ACTION_TYPE_POSE_INPUT);
    MAKE(g_actFire,   "fire",   "Shoot",           XR_ACTION_TYPE_BOOLEAN_INPUT);
    MAKE(g_actStart,  "start",  "Start / Enter",   XR_ACTION_TYPE_BOOLEAN_INPUT);
    MAKE(g_actBack,   "back",   "Back / Escape",   XR_ACTION_TYPE_BOOLEAN_INPUT);
    MAKE(g_actToggle, "screen", "Floating screen", XR_ACTION_TYPE_BOOLEAN_INPUT);
    MAKE(g_actGrip,   "recentre", "Recentre",      XR_ACTION_TYPE_FLOAT_INPUT);
    MAKE(g_actZoom,   "zoom",     "Zoom (toggle)",    XR_ACTION_TYPE_FLOAT_INPUT);
#undef MAKE

    /* the runtime coerces float sources to booleans and back where needed */
    bn = 0;
    BIND(g_actAim,  "/user/hand/left/input/aim/pose");
    BIND(g_actAim,  "/user/hand/right/input/aim/pose");
    BIND(g_actFire, "/user/hand/left/input/select/click");
    BIND(g_actFire, "/user/hand/right/input/select/click");
    BIND(g_actStart, "/user/hand/left/input/menu/click");
    BIND(g_actStart, "/user/hand/right/input/menu/click");
    suggest(inst, "/interaction_profiles/khr/simple_controller", bb, bn);

    bn = 0;
    BIND(g_actAim,  "/user/hand/left/input/aim/pose");
    BIND(g_actAim,  "/user/hand/right/input/aim/pose");
    BIND(g_actFire, "/user/hand/left/input/trigger/value");
    BIND(g_actFire, "/user/hand/right/input/trigger/value");
    BIND(g_actStart, "/user/hand/left/input/x/click");
    BIND(g_actStart, "/user/hand/right/input/a/click");
    BIND(g_actBack,  "/user/hand/left/input/y/click");
    BIND(g_actBack,  "/user/hand/right/input/b/click");
    BIND(g_actToggle, "/user/hand/left/input/thumbstick/click");
    BIND(g_actToggle, "/user/hand/right/input/thumbstick/click");
    BIND(g_actGrip, "/user/hand/left/input/squeeze/value");
    BIND(g_actGrip, "/user/hand/right/input/squeeze/value");
    BIND(g_actZoom, "/user/hand/left/input/thumbstick/y");
    BIND(g_actZoom, "/user/hand/right/input/thumbstick/y");
    suggest(inst, "/interaction_profiles/oculus/touch_controller", bb, bn);

    bn = 0;
    BIND(g_actAim,  "/user/hand/left/input/aim/pose");
    BIND(g_actAim,  "/user/hand/right/input/aim/pose");
    BIND(g_actFire, "/user/hand/left/input/trigger/value");
    BIND(g_actFire, "/user/hand/right/input/trigger/value");
    BIND(g_actStart, "/user/hand/left/input/a/click");
    BIND(g_actStart, "/user/hand/right/input/a/click");
    BIND(g_actBack,  "/user/hand/left/input/b/click");
    BIND(g_actBack,  "/user/hand/right/input/b/click");
    BIND(g_actToggle, "/user/hand/left/input/thumbstick/click");
    BIND(g_actToggle, "/user/hand/right/input/thumbstick/click");
    BIND(g_actGrip, "/user/hand/left/input/squeeze/value");
    BIND(g_actGrip, "/user/hand/right/input/squeeze/value");
    BIND(g_actZoom, "/user/hand/left/input/thumbstick/y");
    BIND(g_actZoom, "/user/hand/right/input/thumbstick/y");
    suggest(inst, "/interaction_profiles/valve/index_controller", bb, bn);

    bn = 0;
    BIND(g_actAim,  "/user/hand/left/input/aim/pose");
    BIND(g_actAim,  "/user/hand/right/input/aim/pose");
    BIND(g_actFire, "/user/hand/left/input/trigger/value");
    BIND(g_actFire, "/user/hand/right/input/trigger/value");
    BIND(g_actStart, "/user/hand/left/input/trackpad/click");
    BIND(g_actStart, "/user/hand/right/input/trackpad/click");
    BIND(g_actBack,  "/user/hand/left/input/menu/click");
    BIND(g_actBack,  "/user/hand/right/input/menu/click");
    BIND(g_actGrip, "/user/hand/left/input/squeeze/click");
    BIND(g_actGrip, "/user/hand/right/input/squeeze/click");
    BIND(g_actZoom, "/user/hand/left/input/trackpad/y");
    BIND(g_actZoom, "/user/hand/right/input/trackpad/y");
    suggest(inst, "/interaction_profiles/htc/vive_controller", bb, bn);

    for (h = 0; h < 2; h++) {
        XrActionSpaceCreateInfo si;
        ZeroMemory(&si, sizeof(si));
        si.type = XR_TYPE_ACTION_SPACE_CREATE_INFO;
        si.action = g_actAim;
        si.subactionPath = g_handPath[h];
        si.poseInActionSpace.orientation.w = 1.0f;
        if (XR_FAILED(pxrCreateActionSpace(session, &si, &g_aimSpace[h])))
            die("could not create the aim space");
    }

    ZeroMemory(&at, sizeof(at));
    at.type = XR_TYPE_SESSION_ACTION_SETS_ATTACH_INFO;
    at.countActionSets = 1;
    at.actionSets = &g_actSet;
    if (XR_FAILED(pxrAttachSessionActionSets(session, &at)))
        die("could not attach the action set");
    note("controllers wired: trigger shoot, A/X start, B/Y back,\n"
         "                   stick click screen, grip recentre\n");
}
#undef BIND

/*
 * One tick of controller handling. Returns 1 if the player asked to recentre.
 *
 * The aim ray starts in local (metre) space. If the floating screen is up and
 * the ray lands on it, that intersection maps straight to 640x480 - native
 * menus become directly clickable. Otherwise the ray is moved into game space
 * (the exact inverse of the model matrix runVR builds: undo the recentre
 * translation, undo the yaw, multiply the scale back out), cast against the
 * frame's triangles, and the hit is projected through the game's own camera -
 * which is precisely what a light gun does.
 */
static int handleControllers(XrSession session, XrSpace space, XrTime when,
                             float yaw0, float ox, float oy, float oz)
{
    XrActionsSyncInfo si;
    XrActiveActionSet act;
    XrActionStateGetInfo gi;
    XrActionStateBoolean fire[2], bstart, bback, btoggle;
    XrActionStateFloat grip;
    XrSpaceLocation loc;
    static int prevToggle, prevGrip;
    int recentre = 0, h, hand;
    unsigned buttons = 0;
    float p[3], d[3], fwd[3] = { 0, 0, -1 };
    float hitLocal[3];
    int haveHit = 0;
    float sx = 320.0f, sy = 240.0f;

    ZeroMemory(&act, sizeof(act));
    act.actionSet = g_actSet;
    act.subactionPath = XR_NULL_PATH;
    ZeroMemory(&si, sizeof(si));
    si.type = XR_TYPE_ACTIONS_SYNC_INFO;
    si.countActiveActionSets = 1;
    si.activeActionSets = &act;
    if (pxrSyncActions(session, &si) != XR_SUCCESS) return 0;   /* not focused */

    gameProjRead();     /* the projection the game is using THIS frame */

#define GETB(out, act_, hpath) do {                                       \
        ZeroMemory(&gi, sizeof(gi)); ZeroMemory(&(out), sizeof(out));     \
        gi.type = XR_TYPE_ACTION_STATE_GET_INFO;                          \
        (out).type = XR_TYPE_ACTION_STATE_BOOLEAN;                        \
        gi.action = (act_); gi.subactionPath = (hpath);                   \
        pxrGetActionStateBoolean(session, &gi, &(out));                   \
    } while (0)

    GETB(fire[0], g_actFire, g_handPath[0]);
    GETB(fire[1], g_actFire, g_handPath[1]);
    GETB(bstart, g_actStart, XR_NULL_PATH);
    GETB(bback, g_actBack, XR_NULL_PATH);
    GETB(btoggle, g_actToggle, XR_NULL_PATH);
#undef GETB
    ZeroMemory(&gi, sizeof(gi)); ZeroMemory(&grip, sizeof(grip));
    gi.type = XR_TYPE_ACTION_STATE_GET_INFO;
    grip.type = XR_TYPE_ACTION_STATE_FLOAT;
    gi.action = g_actGrip; gi.subactionPath = XR_NULL_PATH;
    pxrGetActionStateFloat(session, &gi, &grip);

    /* zoom: flick the thumbstick up to toggle the scope on, flick again to
     * drop it. A held stick as an analogue zoom turned out nauseating - the
     * level breathed with every wobble of the thumb - and the snap between
     * levels was worse. Now it is a latch, and the glide toward the target is
     * slow (zoomspeed percent of the remaining gap per frame; 4 at 90 Hz
     * settles in about a second) so the world swells instead of jumping. */
    {
        XrActionStateFloat z; float push = 0.0f, targetZoom; int hh, pressed;
        static int zoomOn, zoomHeld;
        for (hh = 0; hh < 2; hh++) {
            ZeroMemory(&gi, sizeof(gi)); ZeroMemory(&z, sizeof(z));
            gi.type = XR_TYPE_ACTION_STATE_GET_INFO;
            z.type = XR_TYPE_ACTION_STATE_FLOAT;
            gi.action = g_actZoom; gi.subactionPath = g_handPath[hh];
            if (pxrGetActionStateFloat(session, &gi, &z) == XR_SUCCESS &&
                z.isActive && z.currentState > push)
                push = z.currentState;               /* up only, 0..1 */
        }
        /* hysteresis: latch at a firm push, re-arm only near the centre */
        pressed = zoomHeld ? (push > 0.30f) : (push > 0.65f);
        if (pressed && !zoomHeld) zoomOn = !zoomOn;
        zoomHeld = pressed;
        targetZoom = zoomOn ? (float)g_cfgZoomX / 100.0f : 1.0f;
        /* In the flat game the zoom moments were authored: the engine walks
         * its fov from 60 down to ~18 degrees exactly when a distant enemy is
         * meant to fill the screen, and the player just keeps shooting. Here
         * the reconstruction stays true-scale through that (correct for the
         * world, useless for the fight), so follow the game instead: magnify
         * by the same ratio the game is applying, capped by the zoom key.
         * The player aims, the scope comes to them. */
        if (g_cfgAutoZoom && g_projLive && g_gfxBase > 300.0f &&
            !(g_scrVisible && g_scrHave)) {
            float az = g_gfx / g_gfxBase;
            float cap = (float)g_cfgZoomX / 100.0f;
            if (az > cap) az = cap;
            if (az > targetZoom) targetZoom = az;
        }
        g_zoomLevel += (targetZoom - g_zoomLevel) * ((float)g_cfgZoomSpd / 100.0f);
        if (g_zoomLevel < 1.001f) g_zoomLevel = 1.0f;
    }

    /* the gun is whichever hand fired last */
    for (h = 0; h < 2; h++)
        if (fire[h].isActive && fire[h].currentState && fire[h].changedSinceLastSync)
            g_activeHand = h;
    hand = g_activeHand;

    if (btoggle.isActive && btoggle.currentState && !prevToggle)
        g_scrMode = (g_scrMode + 1) % 3;
    prevToggle = btoggle.isActive && btoggle.currentState;

    if (grip.isActive && grip.currentState > 0.85f && !prevGrip) recentre = 1;
    prevGrip = grip.isActive && grip.currentState > 0.85f;

    if (fire[hand].isActive && fire[hand].currentState) buttons |= VC2_BTN_FIRE;
    if (bstart.isActive && bstart.currentState)         buttons |= VC2_BTN_START;
    if (bback.isActive && bback.currentState)           buttons |= VC2_BTN_BACK;

    /* where is the gun */
    ZeroMemory(&loc, sizeof(loc));
    loc.type = XR_TYPE_SPACE_LOCATION;
    if (XR_FAILED(pxrLocateSpace(g_aimSpace[hand], space, when, &loc)) ||
        !(loc.locationFlags & XR_SPACE_LOCATION_POSITION_VALID_BIT)) {
        hand = 1 - hand;
        ZeroMemory(&loc, sizeof(loc));
        loc.type = XR_TYPE_SPACE_LOCATION;
        if (XR_FAILED(pxrLocateSpace(g_aimSpace[hand], space, when, &loc)) ||
            !(loc.locationFlags & XR_SPACE_LOCATION_POSITION_VALID_BIT)) {
            g_ovCount = 0;
            pushAim(sx, sy, buttons);
            return recentre;
        }
    }
    p[0] = loc.pose.position.x;
    p[1] = loc.pose.position.y;
    p[2] = loc.pose.position.z;
    quatRotate(&loc.pose.orientation, fwd, d);

    /* try the floating screen first */
    if (g_scrVisible && g_scrHave) {
        float toC[3] = { g_scrC[0]-p[0], g_scrC[1]-p[1], g_scrC[2]-p[2] };
        float denom = vDot(d, g_scrN);
        if (denom < -1e-6f || denom > 1e-6f) {
            float t = vDot(toC, g_scrN) / denom;
            if (t > 0.05f) {
                float hp[3] = { p[0]+d[0]*t, p[1]+d[1]*t, p[2]+d[2]*t };
                float rel[3] = { hp[0]-g_scrC[0], hp[1]-g_scrC[1], hp[2]-g_scrC[2] };
                float u = vDot(rel, g_scrR) / g_scrHalfW;
                float v = vDot(rel, g_scrU) / g_scrHalfH;
                if (u > -1.05f && u < 1.05f && v > -1.05f && v < 1.05f) {
                    if (u < -1) u = -1; if (u > 1) u = 1;
                    if (v < -1) v = -1; if (v > 1) v = 1;
                    sx = 320.0f + u * 319.0f;
                    sy = 240.0f - v * 239.0f;
                    hitLocal[0] = hp[0]; hitLocal[1] = hp[1]; hitLocal[2] = hp[2];
                    haveHit = 2;
                }
            }
        }
    }

    /* otherwise into game space and against the level itself */
    if (!haveHit) {
        float cy = cosf(-yaw0), syw = sinf(-yaw0);
        float pl[3] = { p[0]-ox, p[1]-oy, p[2]-oz };
        float pg[3], dg[3], t;
        pg[0] = ( cy*pl[0] + syw*pl[2]) * g_unitsPerMetre;
        pg[1] =   pl[1] * g_unitsPerMetre;
        pg[2] = (-syw*pl[0] + cy*pl[2]) * g_unitsPerMetre;
        dg[0] =  cy*d[0] + syw*d[2];
        dg[1] =  d[1];
        dg[2] = -syw*d[0] + cy*d[2];

        if (!rayVsScene(pg, dg, &t))
            t = (float)g_cfgReach * g_unitsPerMetre;    /* nothing hit */
        {
            float hg[3] = { pg[0]+dg[0]*t, pg[1]+dg[1]*t, pg[2]+dg[2]*t };
            float zv = -hg[2];
            if (zv > 1.0f) {
                /* the exact inverse of the DLL's unproject():
                 * sx = cx + x*fx/z, sy = cy - y*fy/z, all four values live */
                sx = g_gcx + hg[0] * g_gfx / zv;
                sy = g_gcy - hg[1] * g_gfy / zv;
                if (sx < 0) sx = 0; if (sx > 639) sx = 639;
                if (sy < 0) sy = 0; if (sy > 479) sy = 479;
            }
            /* back to local space for the laser */
            {
                float s = 1.0f / g_unitsPerMetre;
                float gx = hg[0]*s, gy = hg[1]*s, gz = hg[2]*s;
                float rc = cosf(yaw0), rs = sinf(yaw0);
                hitLocal[0] = ox + rc*gx + rs*gz;
                hitLocal[1] = oy + gy;
                hitLocal[2] = oz - rs*gx + rc*gz;
                haveHit = 1;
            }
        }
    }

    pushAim(sx, sy, buttons);

    /* the laser and a small cross at the hit point */
    g_ovCount = 0;
    {
        DWORD col = (buttons & VC2_BTN_FIRE) ? 0xFF40C0FFu : 0xFF3838FFu; /* ABGR */
        float mx[3], a[3], b[3];
        ovBeam(p, hitLocal, 0.002f, col);
        mx[0] = hitLocal[0]; mx[1] = hitLocal[1]; mx[2] = hitLocal[2];
        a[0] = mx[0]-0.02f; a[1] = mx[1]; a[2] = mx[2];
        b[0] = mx[0]+0.02f; b[1] = mx[1]; b[2] = mx[2];
        ovBeam(a, b, 0.004f, 0xFF30FF30u);
        a[0] = mx[0]; a[1] = mx[1]-0.02f;
        b[0] = mx[0]; b[1] = mx[1]+0.02f;
        ovBeam(a, b, 0.004f, 0xFF30FF30u);
    }
    return recentre;
}

typedef struct {
    XrSwapchain sc;
    int w, h;
    uint32_t imgCount;
    XrSwapchainImageD3D11KHR *imgs;
    ID3D11RenderTargetView **rtv;   /* views on the runtime's images (resolve targets) */
    ID3D11DepthStencilView *dsv;
    /* with msaa > 1 everything is drawn into msTex and resolved into the
     * runtime's image afterwards; with msaa == 1 msTex stays NULL and the
     * runtime's image is rendered into directly, as before */
    ID3D11Texture2D        *msTex;
    ID3D11RenderTargetView *msRtv;
} Eye;

/* ask the device what it can do; drop to the next level down if refused */
static int pickMsaa(DXGI_FORMAT fmt, int want)
{
    UINT q = 0;
    while (want > 1) {
        if (SUCCEEDED(ID3D11Device_CheckMultisampleQualityLevels(g_dev, fmt,
                      (UINT)want, &q)) && q > 0 &&
            SUCCEEDED(ID3D11Device_CheckMultisampleQualityLevels(g_dev,
                      DXGI_FORMAT_D32_FLOAT, (UINT)want, &q)) && q > 0)
            return want;
        want /= 2;
    }
    return 1;
}

static void makeEyeTargets(Eye *e, DXGI_FORMAT fmt, int msaa)
{
    D3D11_TEXTURE2D_DESC td;
    ID3D11Texture2D *depth = NULL;
    D3D11_RENDER_TARGET_VIEW_DESC rd;
    uint32_t i;

    e->rtv = (ID3D11RenderTargetView **)calloc(e->imgCount, sizeof(void *));
    ZeroMemory(&rd, sizeof(rd));
    rd.Format = fmt;
    rd.ViewDimension = D3D11_RTV_DIMENSION_TEXTURE2D;
    for (i = 0; i < e->imgCount; i++)
        if (FAILED(ID3D11Device_CreateRenderTargetView(g_dev,
                   (ID3D11Resource *)e->imgs[i].texture, &rd, &e->rtv[i])))
            die("render target view for a swapchain image");

    ZeroMemory(&td, sizeof(td));
    td.Width = e->w; td.Height = e->h;
    td.MipLevels = 1; td.ArraySize = 1;
    td.Format = DXGI_FORMAT_D32_FLOAT;
    td.SampleDesc.Count = (UINT)msaa;
    td.Usage = D3D11_USAGE_DEFAULT;
    td.BindFlags = D3D11_BIND_DEPTH_STENCIL;
    if (FAILED(ID3D11Device_CreateTexture2D(g_dev, &td, NULL, &depth))) die("depth texture");
    ID3D11Device_CreateDepthStencilView(g_dev, (ID3D11Resource *)depth, NULL, &e->dsv);
    ID3D11Texture2D_Release(depth);

    if (msaa > 1) {
        ZeroMemory(&td, sizeof(td));
        td.Width = e->w; td.Height = e->h;
        td.MipLevels = 1; td.ArraySize = 1;
        td.Format = fmt;
        td.SampleDesc.Count = (UINT)msaa;
        td.Usage = D3D11_USAGE_DEFAULT;
        td.BindFlags = D3D11_BIND_RENDER_TARGET;
        if (FAILED(ID3D11Device_CreateTexture2D(g_dev, &td, NULL, &e->msTex)))
            die("msaa colour target");
        if (FAILED(ID3D11Device_CreateRenderTargetView(g_dev,
                   (ID3D11Resource *)e->msTex, NULL, &e->msRtv)))
            die("msaa render target view");
    }
}

static int runVR(void)
{
    HMODULE loader;
    XrInstance inst = XR_NULL_HANDLE;
    XrSystemId sys = XR_NULL_SYSTEM_ID;
    XrSession session = XR_NULL_HANDLE;
    XrSpace space = XR_NULL_HANDLE;
    XrSessionState state = XR_SESSION_STATE_UNKNOWN;
    XrInstanceCreateInfo ici;
    XrSystemGetInfo sgi;
    XrGraphicsRequirementsD3D11KHR req;
    XrGraphicsBindingD3D11KHR bind;
    XrSessionCreateInfo sci;
    XrReferenceSpaceCreateInfo rsci;
    XrViewConfigurationView vcv[2];
    PFN_xrGetD3D11GraphicsRequirementsKHR pGetReq = NULL;
    const char *exts[1] = { XR_KHR_D3D11_ENABLE_EXTENSION_NAME };
    uint32_t n = 0, i;
    Eye eye[2];
    IDXGIFactory1 *fac = NULL;
    IDXGIAdapter1 *ad = NULL, *pick = NULL;
    int64_t *fmts = NULL;
    DXGI_FORMAT chosen = DXGI_FORMAT_R8G8B8A8_UNORM;
    int running = 0, haveOrigin = 0;
    int eyeMsaa[2] = { 1, 1 };
    float originYaw = 0.0f, ox = 0, oy = 0, oz = 0;
    D3D_FEATURE_LEVEL fl;

    loader = LoadLibraryA("openxr_loader.dll");
    if (!loader)
        die("openxr_loader.dll not found. Put it next to VC2VR.exe - it comes from\n"
            "       the Khronos OpenXR SDK release, github.com/KhronosGroup/OpenXR-SDK/releases\n"
            "       (the 64-bit one, from x64/bin inside the zip)");
    xrGIPA = (PFN_xrGetInstanceProcAddr)GetProcAddress(loader, "xrGetInstanceProcAddr");
    if (!xrGIPA) die("openxr_loader.dll has no xrGetInstanceProcAddr - wrong file?");
    if (XR_FAILED(xrGIPA(XR_NULL_HANDLE, "xrCreateInstance",
                         (PFN_xrVoidFunction *)&pxrCreateInstance)))
        die("the loader would not hand over xrCreateInstance");
    xrGIPA(XR_NULL_HANDLE, "xrEnumerateInstanceExtensionProperties",
           (PFN_xrVoidFunction *)&pxrEnumerateInstanceExtensionProperties);

    /* say what the runtime offers before asking it for anything */
    if (pxrEnumerateInstanceExtensionProperties) {
        uint32_t cnt = 0, k;
        XrExtensionProperties *ep;
        int haveD3D11 = 0;
        pxrEnumerateInstanceExtensionProperties(NULL, 0, &cnt, NULL);
        note("runtime offers %u extensions\n", cnt);
        if (cnt) {
            ep = (XrExtensionProperties *)calloc(cnt, sizeof(XrExtensionProperties));
            for (k = 0; k < cnt; k++) ep[k].type = XR_TYPE_EXTENSION_PROPERTIES;
            pxrEnumerateInstanceExtensionProperties(NULL, cnt, &cnt, ep);
            for (k = 0; k < cnt; k++)
                if (!lstrcmpA(ep[k].extensionName, XR_KHR_D3D11_ENABLE_EXTENSION_NAME))
                    haveD3D11 = 1;
            free(ep);
        }
        if (!haveD3D11)
            note("  warning: this runtime does not list %s\n",
                 XR_KHR_D3D11_ENABLE_EXTENSION_NAME);
    }

    /* Ask for 1.0 first. SteamVR implements OpenXR 1.0 and refuses a 1.1
     * request outright, which is what the earlier build ran into. */
    {
        XrVersion tries[2];
        XrResult res = XR_ERROR_RUNTIME_FAILURE;
        int k;
        tries[0] = XR_MAKE_VERSION(1, 0, 0);
        tries[1] = XR_CURRENT_API_VERSION;
        for (k = 0; k < 2; k++) {
            ZeroMemory(&ici, sizeof(ici));
            ici.type = XR_TYPE_INSTANCE_CREATE_INFO;
            ici.applicationInfo.apiVersion = tries[k];
            lstrcpyA(ici.applicationInfo.applicationName, "VirtuaCop2 VR");
            ici.applicationInfo.applicationVersion = 1;
            lstrcpyA(ici.applicationInfo.engineName, "vc2vr");
            ici.enabledExtensionCount = 1;
            ici.enabledExtensionNames = exts;
            res = pxrCreateInstance(&ici, &inst);
            note("xrCreateInstance with api %u.%u -> %d %s\n",
                 (unsigned)XR_VERSION_MAJOR(tries[k]),
                 (unsigned)XR_VERSION_MINOR(tries[k]), (int)res, xrName(res));
            if (XR_SUCCEEDED(res)) break;
        }
        if (XR_FAILED(res))
            die("the runtime refused to start.\n"
                "       With SteamVR this usually means there is no headset. Turn on the\n"
                "       null driver so SteamVR runs with a virtual one - see CHITAT.txt.");
    }
    note("openxr instance ok\n");
    loadXr(inst);
    xrGIPA(inst, "xrGetD3D11GraphicsRequirementsKHR", (PFN_xrVoidFunction *)&pGetReq);
    if (!pGetReq) die("the runtime does not offer D3D11 support");

    ZeroMemory(&sgi, sizeof(sgi));
    sgi.type = XR_TYPE_SYSTEM_GET_INFO;
    sgi.formFactor = XR_FORM_FACTOR_HEAD_MOUNTED_DISPLAY;
    {
        XrResult res = pxrGetSystem(inst, &sgi, &sys);
        if (XR_FAILED(res)) {
            note("xrGetSystem -> %d %s\n", (int)res, xrName(res));
            die("no headset. Either connect one, or turn on the SteamVR null driver\n"
                "       to get a virtual headset - see CHITAT.txt.");
        }
    }
    note("headset found\n");

    ZeroMemory(&req, sizeof(req));
    req.type = XR_TYPE_GRAPHICS_REQUIREMENTS_D3D11_KHR;
    pGetReq(inst, sys, &req);

    /* the runtime dictates which GPU to render on */
    if (FAILED(CreateDXGIFactory1(&IID_IDXGIFactory1, (void **)&fac))) die("dxgi factory");
    for (i = 0; IDXGIFactory1_EnumAdapters1(fac, i, &ad) == S_OK; i++) {
        DXGI_ADAPTER_DESC1 d;
        IDXGIAdapter1_GetDesc1(ad, &d);
        if (d.AdapterLuid.LowPart == req.adapterLuid.LowPart &&
            d.AdapterLuid.HighPart == req.adapterLuid.HighPart) { pick = ad; break; }
        IDXGIAdapter1_Release(ad);
    }
    if (!pick) die("the GPU the runtime asked for is not present");
    if (FAILED(D3D11CreateDevice((IDXGIAdapter *)pick, D3D_DRIVER_TYPE_UNKNOWN, NULL, 0,
              &req.minFeatureLevel, 1, D3D11_SDK_VERSION, &g_dev, &fl, &g_ctx)))
        die("could not create a D3D11 device on that GPU");
    makePipeline();
    note("d3d11 ok\n");

    ZeroMemory(&bind, sizeof(bind));
    bind.type = XR_TYPE_GRAPHICS_BINDING_D3D11_KHR;
    bind.device = g_dev;
    ZeroMemory(&sci, sizeof(sci));
    sci.type = XR_TYPE_SESSION_CREATE_INFO;
    sci.next = &bind;
    sci.systemId = sys;
    if (XR_FAILED(pxrCreateSession(inst, &sci, &session))) die("could not create the session");

    ZeroMemory(&rsci, sizeof(rsci));
    rsci.type = XR_TYPE_REFERENCE_SPACE_CREATE_INFO;
    rsci.referenceSpaceType = XR_REFERENCE_SPACE_TYPE_LOCAL;
    rsci.poseInReferenceSpace.orientation.w = 1.0f;
    if (XR_FAILED(pxrCreateReferenceSpace(session, &rsci, &space))) die("reference space");

    initActions(inst, session);

    for (i = 0; i < 2; i++) { ZeroMemory(&vcv[i], sizeof(vcv[i])); vcv[i].type = XR_TYPE_VIEW_CONFIGURATION_VIEW; }
    n = 2;
    pxrEnumerateViewConfigurationViews(inst, sys,
        XR_VIEW_CONFIGURATION_TYPE_PRIMARY_STEREO, 2, &n, vcv);
    note("eye buffers %ux%u\n", vcv[0].recommendedImageRectWidth,
         vcv[0].recommendedImageRectHeight);

    /* pick a colour format the runtime actually offers */
    n = 0;
    pxrEnumerateSwapchainFormats(session, 0, &n, NULL);
    fmts = (int64_t *)calloc(n ? n : 1, sizeof(int64_t));
    pxrEnumerateSwapchainFormats(session, n, &n, fmts);
    for (i = 0; i < n; i++)
        if (fmts[i] == DXGI_FORMAT_R8G8B8A8_UNORM_SRGB ||
            fmts[i] == DXGI_FORMAT_B8G8R8A8_UNORM_SRGB ||
            fmts[i] == DXGI_FORMAT_R8G8B8A8_UNORM) { chosen = (DXGI_FORMAT)fmts[i]; break; }

    {
        int msaa = pickMsaa(chosen, g_cfgMsaa);
        note("msaa x%d, eye buffer scale %d%%\n", msaa, g_cfgSuper);
        for (i = 0; i < 2; i++) eyeMsaa[i] = msaa;
    }
    for (i = 0; i < 2; i++) {
        XrSwapchainCreateInfo ci;
        uint32_t k, cnt = 0, sw, sh;
        ZeroMemory(&ci, sizeof(ci));
        ci.type = XR_TYPE_SWAPCHAIN_CREATE_INFO;
        ci.usageFlags = XR_SWAPCHAIN_USAGE_COLOR_ATTACHMENT_BIT;
        ci.format = chosen;
        ci.sampleCount = 1;
        sw = vcv[i].recommendedImageRectWidth  * (uint32_t)g_cfgSuper / 100u;
        sh = vcv[i].recommendedImageRectHeight * (uint32_t)g_cfgSuper / 100u;
        if (vcv[i].maxImageRectWidth  && sw > vcv[i].maxImageRectWidth)  sw = vcv[i].maxImageRectWidth;
        if (vcv[i].maxImageRectHeight && sh > vcv[i].maxImageRectHeight) sh = vcv[i].maxImageRectHeight;
        ci.width = sw;
        ci.height = sh;
        ci.faceCount = 1; ci.arraySize = 1; ci.mipCount = 1;
        ZeroMemory(&eye[i], sizeof(eye[i]));
        if (XR_FAILED(pxrCreateSwapchain(session, &ci, &eye[i].sc))) die("swapchain");
        eye[i].w = ci.width; eye[i].h = ci.height;
        pxrEnumerateSwapchainImages(eye[i].sc, 0, &cnt, NULL);
        eye[i].imgCount = cnt;
        eye[i].imgs = (XrSwapchainImageD3D11KHR *)calloc(cnt, sizeof(XrSwapchainImageD3D11KHR));
        for (k = 0; k < cnt; k++) eye[i].imgs[k].type = XR_TYPE_SWAPCHAIN_IMAGE_D3D11_KHR;
        pxrEnumerateSwapchainImages(eye[i].sc, cnt, &cnt,
                                    (XrSwapchainImageBaseHeader *)eye[i].imgs);
        makeEyeTargets(&eye[i], chosen, eyeMsaa[i]);
    }
    note("session ready - put the headset on\n");

    for (;;) {
        XrEventDataBuffer ev;
        XrFrameWaitInfo fwi = { XR_TYPE_FRAME_WAIT_INFO };
        XrFrameState fs = { XR_TYPE_FRAME_STATE };
        XrFrameBeginInfo fbi = { XR_TYPE_FRAME_BEGIN_INFO };
        XrFrameEndInfo fei = { XR_TYPE_FRAME_END_INFO };
        XrViewLocateInfo vli = { XR_TYPE_VIEW_LOCATE_INFO };
        XrViewState vs = { XR_TYPE_VIEW_STATE };
        XrView views[2];
        XrCompositionLayerProjectionView pv[2];
        XrCompositionLayerProjection layer = { XR_TYPE_COMPOSITION_LAYER_PROJECTION };
        const XrCompositionLayerBaseHeader *layers[1];
        uint32_t got = 0;

        for (;;) {
            ZeroMemory(&ev, sizeof(ev));
            ev.type = XR_TYPE_EVENT_DATA_BUFFER;
            if (pxrPollEvent(inst, &ev) != XR_SUCCESS) break;
            if (ev.type == XR_TYPE_EVENT_DATA_SESSION_STATE_CHANGED) {
                XrEventDataSessionStateChanged *s = (XrEventDataSessionStateChanged *)&ev;
                state = s->state;
                if (state == XR_SESSION_STATE_READY) {
                    XrSessionBeginInfo bi = { XR_TYPE_SESSION_BEGIN_INFO };
                    bi.primaryViewConfigurationType = XR_VIEW_CONFIGURATION_TYPE_PRIMARY_STEREO;
                    pxrBeginSession(session, &bi);
                    running = 1;
                    note("session running\n");
                } else if (state == XR_SESSION_STATE_STOPPING) {
                    pxrEndSession(session);
                    running = 0;
                } else if (state == XR_SESSION_STATE_EXITING ||
                           state == XR_SESSION_STATE_LOSS_PENDING) {
                    note("session ended\n");
                    return 0;
                }
            }
        }
        if (!running) { Sleep(20); continue; }

        pxrWaitFrame(session, &fwi, &fs);
        pxrBeginFrame(session, &fbi);
        pullFrame();
        pullScreen();
        pullAtlas();

        /* the screen shows itself whenever the 3D scene is nearly empty -
         * that is the menus, the scores, the name entry, the attract mode */
        g_scrVisible = (g_scrMode == 1) ||
                       (g_scrMode == 0 && g_localCount < 900);

        for (i = 0; i < 2; i++) { ZeroMemory(&views[i], sizeof(views[i])); views[i].type = XR_TYPE_VIEW; }
        vli.viewConfigurationType = XR_VIEW_CONFIGURATION_TYPE_PRIMARY_STEREO;
        vli.displayTime = fs.predictedDisplayTime;
        vli.space = space;
        pxrLocateViews(session, &vli, &vs, 2, &got, views);

        if (fs.shouldRender && got == 2) {
            float scale = 1.0f / g_unitsPerMetre;
            float model[16], t[16], rot[16], tmp[16];

            /* the first head pose becomes the game camera: the player starts
             * standing where the in-game viewpoint is, facing the same way */
            if (!haveOrigin) {
                const XrQuaternionf *q = &views[0].pose.orientation;
                originYaw = atan2f(2.0f * (q->w * q->y + q->x * q->z),
                                   1.0f - 2.0f * (q->y * q->y + q->x * q->x));
                ox = views[0].pose.position.x;
                oy = views[0].pose.position.y;
                oz = views[0].pose.position.z;
                haveOrigin = 1;
                setScreenPose(ox, oy, oz, originYaw);
                note("recentred on the current head pose\n");
            }

            if (handleControllers(session, space, fs.predictedDisplayTime,
                                  originYaw, ox, oy, oz))
                haveOrigin = 0;                    /* grip: recentre next frame */

            mIdent(model);
            model[0] = model[5] = model[10] = scale;
            mIdent(rot);
            rot[0] = cosf(originYaw);  rot[2]  = sinf(originYaw);
            rot[8] = -sinf(originYaw); rot[10] = cosf(originYaw);
            mIdent(t);
            t[3] = ox; t[7] = oy; t[11] = oz;
            mMul(rot, model, tmp);
            mMul(t, tmp, model);

            uploadVerts();
            uploadOverlay();
            uploadScreenTex();
            uploadAtlasTex();
            for (i = 0; i < 2; i++) {
                uint32_t idx = 0;
                XrSwapchainImageAcquireInfo ai = { XR_TYPE_SWAPCHAIN_IMAGE_ACQUIRE_INFO };
                XrSwapchainImageWaitInfo wi = { XR_TYPE_SWAPCHAIN_IMAGE_WAIT_INFO };
                XrSwapchainImageReleaseInfo ri = { XR_TYPE_SWAPCHAIN_IMAGE_RELEASE_INFO };
                float view[16], proj[16], mvp[16], vp[16];

                pxrAcquireSwapchainImage(eye[i].sc, &ai, &idx);
                wi.timeout = XR_INFINITE_DURATION;
                pxrWaitSwapchainImage(eye[i].sc, &wi);

                mView(&views[i].pose, view);
                {
                    float z = g_zoomLevel;              /* 1 = none, held stick raises it */
                    float aL = views[i].fov.angleLeft, aR = views[i].fov.angleRight;
                    float aU = views[i].fov.angleUp,   aD = views[i].fov.angleDown;
                    if (z > 1.001f) {                   /* narrow the frustum = magnify */
                        aL = atanf(tanf(aL) / z); aR = atanf(tanf(aR) / z);
                        aU = atanf(tanf(aU) / z); aD = atanf(tanf(aD) / z);
                    }
                    mProjFov(aL, aR, aU, aD, NEAR_M, FAR_M, proj);
                }
                mMul(proj, view, vp);              /* UI lives in local space */
                mMul(view, model, mvp);
                mMul(proj, mvp, mvp);
                {
                    ID3D11RenderTargetView *target =
                        eye[i].msRtv ? eye[i].msRtv : eye[i].rtv[idx];
                    drawWith(target, eye[i].dsv, eye[i].w, eye[i].h, mvp);
                    drawUI(vp);
                    if (eye[i].msRtv)
                        ID3D11DeviceContext_ResolveSubresource(g_ctx,
                            (ID3D11Resource *)eye[i].imgs[idx].texture, 0,
                            (ID3D11Resource *)eye[i].msTex, 0, chosen);
                }
                pxrReleaseSwapchainImage(eye[i].sc, &ri);

                ZeroMemory(&pv[i], sizeof(pv[i]));
                pv[i].type = XR_TYPE_COMPOSITION_LAYER_PROJECTION_VIEW;
                pv[i].pose = views[i].pose;
                pv[i].fov = views[i].fov;
                pv[i].subImage.swapchain = eye[i].sc;
                pv[i].subImage.imageRect.extent.width = eye[i].w;
                pv[i].subImage.imageRect.extent.height = eye[i].h;
            }
            layer.space = space;
            layer.viewCount = 2;
            layer.views = pv;
            layers[0] = (const XrCompositionLayerBaseHeader *)&layer;
            fei.layerCount = 1;
            fei.layers = layers;
        }
        fei.type = XR_TYPE_FRAME_END_INFO;
        fei.displayTime = fs.predictedDisplayTime;
        fei.environmentBlendMode = XR_ENVIRONMENT_BLEND_MODE_OPAQUE;
        pxrEndFrame(session, &fei);
    }
}

/* ------------------------------------------------------- plain window mode */

static float w_yaw, w_pitch, w_x, w_y, w_z, w_speed = 2.0f;
static int   g_recentre;
static BOOL  w_drag;
static POINT w_from;

static LRESULT CALLBACK wp(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_LBUTTONDOWN: w_drag = TRUE; w_from.x = LOWORD(l); w_from.y = HIWORD(l); SetCapture(h); return 0;
    case WM_LBUTTONUP:   w_drag = FALSE; ReleaseCapture(); return 0;
    case WM_MOUSEMOVE:
        if (w_drag) {
            int x = (short)LOWORD(l), y = (short)HIWORD(l);
            w_yaw += (x - w_from.x) * 0.005f;
            w_pitch += (y - w_from.y) * 0.005f;
            w_from.x = x; w_from.y = y;
        }
        return 0;
    case WM_MOUSEWHEEL: w_speed *= ((short)HIWORD(w) > 0) ? 1.4f : 0.71f; return 0;
    case WM_KEYDOWN: {
        float cy = cosf(w_yaw), sy = sinf(w_yaw), s = w_speed;
        if (w == 'W') { w_x -= sy * s; w_z -= cy * s; }
        if (w == 'S') { w_x += sy * s; w_z += cy * s; }
        if (w == 'D') { w_x += cy * s; w_z -= sy * s; }
        if (w == 'A') { w_x -= cy * s; w_z += sy * s; }
        if (w == 'R') { w_yaw = w_pitch = w_x = w_y = w_z = 0.0f; g_recentre = 1; }
        if (w == 'M') g_scrMode = (g_scrMode + 1) % 3;
        if (w == VK_ESCAPE) PostQuitMessage(0);
        return 0;
    }
    case WM_DESTROY: PostQuitMessage(0); return 0;
    }
    return DefWindowProcA(h, m, w, l);
}

static int runWindow(void)
{
    WNDCLASSA wc;
    HWND hwnd;
    DXGI_SWAP_CHAIN_DESC sd;
    IDXGISwapChain *swap = NULL;
    ID3D11RenderTargetView *rtv = NULL;
    ID3D11DepthStencilView *dsv = NULL;
    ID3D11Texture2D *back = NULL, *depth = NULL;
    D3D11_TEXTURE2D_DESC td;
    D3D_FEATURE_LEVEL fl;
    MSG msg;
    int W = 1280, H = 720;

    ZeroMemory(&wc, sizeof(wc));
    wc.lpfnWndProc = wp;
    wc.hInstance = GetModuleHandleA(NULL);
    wc.hCursor = LoadCursorA(NULL, (LPCSTR)IDC_ARROW);
    wc.lpszClassName = "VC2VRWin";
    RegisterClassA(&wc);
    {
        RECT r = { 0, 0, W, H };        /* W x H of actual picture, not frame */
        AdjustWindowRect(&r, WS_OVERLAPPEDWINDOW, FALSE);
        hwnd = CreateWindowExA(0, "VC2VRWin", "VC2VR - window mode", WS_OVERLAPPEDWINDOW,
                               CW_USEDEFAULT, CW_USEDEFAULT,
                               r.right - r.left, r.bottom - r.top,
                               NULL, NULL, wc.hInstance, NULL);
    }
    ShowWindow(hwnd, SW_SHOW);

    ZeroMemory(&sd, sizeof(sd));
    sd.BufferCount = 2;
    sd.BufferDesc.Width = W; sd.BufferDesc.Height = H;
    sd.BufferDesc.Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    sd.BufferUsage = DXGI_USAGE_RENDER_TARGET_OUTPUT;
    sd.OutputWindow = hwnd;
    sd.SampleDesc.Count = 1;
    sd.Windowed = TRUE;
    sd.SwapEffect = DXGI_SWAP_EFFECT_DISCARD;
    if (FAILED(D3D11CreateDeviceAndSwapChain(NULL, D3D_DRIVER_TYPE_HARDWARE, NULL, 0,
              NULL, 0, D3D11_SDK_VERSION, &sd, &swap, &g_dev, &fl, &g_ctx)))
        die("d3d11 device");
    makePipeline();

    IDXGISwapChain_GetBuffer(swap, 0, &IID_ID3D11Texture2D, (void **)&back);
    ID3D11Device_CreateRenderTargetView(g_dev, (ID3D11Resource *)back, NULL, &rtv);
    ID3D11Texture2D_Release(back);
    ZeroMemory(&td, sizeof(td));
    td.Width = W; td.Height = H; td.MipLevels = 1; td.ArraySize = 1;
    td.Format = DXGI_FORMAT_D32_FLOAT; td.SampleDesc.Count = 1;
    td.Usage = D3D11_USAGE_DEFAULT; td.BindFlags = D3D11_BIND_DEPTH_STENCIL;
    ID3D11Device_CreateTexture2D(g_dev, &td, NULL, &depth);
    ID3D11Device_CreateDepthStencilView(g_dev, (ID3D11Resource *)depth, NULL, &dsv);
    ID3D11Texture2D_Release(depth);

    setScreenPose(0.0f, 0.0f, 0.0f, 0.0f);      /* screen 2 m ahead of origin */

    note("window mode - W A S D, drag to look, R to reset, Esc to quit\n");
    for (;;) {
        float view[16], proj[16], model[16], mvp[16], t[16], rx[16], ry[16], tmp[16];
        float vp2[16];
        float scale, aspect = (float)W / (float)H, fovY = 1.2f;
        char title[200];

        while (PeekMessageA(&msg, NULL, 0, 0, PM_REMOVE)) {
            if (msg.message == WM_QUIT) return 0;
            TranslateMessage(&msg);
            DispatchMessageA(&msg);
        }
        pullFrame();
        pullScreen();
        pullAtlas();
        g_scrVisible = (g_scrMode == 1) ||
                       (g_scrMode == 0 && g_localCount < 900);
        scale = 1.0f / g_unitsPerMetre;

        mIdent(model);
        model[0] = model[5] = model[10] = scale;

        mIdent(t); t[3] = -w_x; t[7] = -w_y; t[11] = -w_z;
        mIdent(ry);
        ry[0] = cosf(w_yaw); ry[2] = -sinf(w_yaw);
        ry[8] = sinf(w_yaw); ry[10] = cosf(w_yaw);
        mIdent(rx);
        rx[5] = cosf(w_pitch); rx[6] = sinf(w_pitch);
        rx[9] = -sinf(w_pitch); rx[10] = cosf(w_pitch);
        mMul(rx, ry, tmp);
        mMul(tmp, t, view);

        mProjFov(-atanf(aspect * tanf(fovY / 2)), atanf(aspect * tanf(fovY / 2)),
                 fovY / 2, -fovY / 2, NEAR_M, FAR_M, proj);

        mMul(proj, view, vp2);
        mMul(view, model, mvp);
        mMul(proj, mvp, mvp);

        uploadVerts();
        uploadScreenTex();
        uploadAtlasTex();
        drawWith(rtv, dsv, W, H, mvp);
        drawUI(vp2);
        IDXGISwapChain_Present(swap, 1, 0);

        wsprintfA(title, "VC2VR window - game frame %u - %u tris - %d units/m",
                  g_lastFrame, g_localCount / 3, (int)g_unitsPerMetre);
        SetWindowTextA(hwnd, title);
    }
}

/* --------------------------------------------------------------- stereo test
 * The null driver is a poor stand-in: no tracked controllers, a fixed pose,
 * and SteamVR puts the session to sleep the moment focus leaves. What it is
 * really being asked to prove is that the TWO EYE path works - the poses, the
 * asymmetric projections, the recentring, the model matrix that carries the
 * game's units into metres. None of that needs a runtime.
 *
 * So do it here: synthesise a head pose from the mouse and WASD, split it into
 * two eyes an IPD apart, and run EXACTLY the arithmetic runVR runs - mView on
 * a pose, mProjFov on four angles, the same model matrix, the same drawWith
 * and drawUI. What is left untested afterwards is the OpenXR session itself
 * and controller input, and no amount of software can test those without the
 * hardware. Everything else is on screen, both eyes, side by side. */
static int runStereo(void)
{
    WNDCLASSA wc;
    HWND hwnd;
    DXGI_SWAP_CHAIN_DESC sd;
    IDXGISwapChain *swap = NULL;
    ID3D11RenderTargetView *rtv = NULL;
    ID3D11DepthStencilView *dsv = NULL;
    ID3D11Texture2D *back = NULL, *depth = NULL;
    D3D11_TEXTURE2D_DESC td;
    D3D_FEATURE_LEVEL fl;
    MSG msg;
    int W = 1600, H = 600, half = 800;
    int haveOrigin = 0;
    float originYaw = 0.0f, ox = 0.0f, oy = 0.0f, oz = 0.0f;
    float ipd = 0.064f;

    ZeroMemory(&wc, sizeof(wc));
    wc.lpfnWndProc = wp;
    wc.hInstance = GetModuleHandleA(NULL);
    wc.hCursor = LoadCursorA(NULL, (LPCSTR)IDC_ARROW);
    wc.lpszClassName = "VC2VRStereo";
    RegisterClassA(&wc);
    {
        RECT r = { 0, 0, W, H };
        AdjustWindowRect(&r, WS_OVERLAPPEDWINDOW, FALSE);
        hwnd = CreateWindowExA(0, "VC2VRStereo", "VC2VR - stereo test",
                               WS_OVERLAPPEDWINDOW, CW_USEDEFAULT, CW_USEDEFAULT,
                               r.right - r.left, r.bottom - r.top,
                               NULL, NULL, wc.hInstance, NULL);
    }
    ShowWindow(hwnd, SW_SHOW);

    ZeroMemory(&sd, sizeof(sd));
    sd.BufferCount = 2;
    sd.BufferDesc.Width = W; sd.BufferDesc.Height = H;
    sd.BufferDesc.Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    sd.BufferUsage = DXGI_USAGE_RENDER_TARGET_OUTPUT;
    sd.OutputWindow = hwnd;
    sd.SampleDesc.Count = 1;
    sd.Windowed = TRUE;
    sd.SwapEffect = DXGI_SWAP_EFFECT_DISCARD;
    if (FAILED(D3D11CreateDeviceAndSwapChain(NULL, D3D_DRIVER_TYPE_HARDWARE, NULL, 0,
              NULL, 0, D3D11_SDK_VERSION, &sd, &swap, &g_dev, &fl, &g_ctx)))
        die("d3d11 device");
    makePipeline();

    IDXGISwapChain_GetBuffer(swap, 0, &IID_ID3D11Texture2D, (void **)&back);
    ID3D11Device_CreateRenderTargetView(g_dev, (ID3D11Resource *)back, NULL, &rtv);
    ID3D11Texture2D_Release(back);
    ZeroMemory(&td, sizeof(td));
    td.Width = W; td.Height = H; td.MipLevels = 1; td.ArraySize = 1;
    td.Format = DXGI_FORMAT_D32_FLOAT; td.SampleDesc.Count = 1;
    td.Usage = D3D11_USAGE_DEFAULT; td.BindFlags = D3D11_BIND_DEPTH_STENCIL;
    ID3D11Device_CreateTexture2D(g_dev, &td, NULL, &depth);
    ID3D11Device_CreateDepthStencilView(g_dev, (ID3D11Resource *)depth, NULL, &dsv);
    ID3D11Texture2D_Release(depth);

    note("stereo test - left eye left, right eye right\n");
    note("W A S D move, drag to look, R recentre, Esc quit\n");
    note("hold a card between the halves and cross your eyes to check depth\n");

    for (;;) {
        XrPosef head, eyePose[2];
        float model[16], t[16], rot[16], tmp[16];
        float scale, aspect = (float)half / (float)H, fovY = 1.6f;
        float cy2, sy2, cp2, sp2, rightX, rightZ;
        char title[220];
        int i;

        while (PeekMessageA(&msg, NULL, 0, 0, PM_REMOVE)) {
            if (msg.message == WM_QUIT) return 0;
            TranslateMessage(&msg);
            DispatchMessageA(&msg);
        }
        pullFrame();
        pullScreen();
        pullAtlas();
        g_scrVisible = (g_scrMode == 1) ||
                       (g_scrMode == 0 && g_localCount < 900);

        /* a head pose built the way a runtime would report one */
        cy2 = cosf(w_yaw * 0.5f); sy2 = sinf(w_yaw * 0.5f);
        cp2 = cosf(w_pitch * 0.5f); sp2 = sinf(w_pitch * 0.5f);
        head.orientation.w = cy2 * cp2;
        head.orientation.x = cy2 * sp2;
        head.orientation.y = sy2 * cp2;
        head.orientation.z = -sy2 * sp2;
        head.position.x = w_x; head.position.y = w_y; head.position.z = w_z;

        rightX =  cosf(w_yaw);          /* head right vector, yaw only */
        rightZ = -sinf(w_yaw);
        for (i = 0; i < 2; i++) {
            float s2 = (i == 0) ? -0.5f : 0.5f;
            eyePose[i] = head;
            eyePose[i].position.x = w_x + rightX * ipd * s2;
            eyePose[i].position.z = w_z + rightZ * ipd * s2;
        }

        /* recentring, exactly as the headset path does it on the first pose */
        if (!haveOrigin) {
            const XrQuaternionf *q = &eyePose[0].orientation;
            originYaw = atan2f(2.0f * (q->w * q->y + q->x * q->z),
                               1.0f - 2.0f * (q->y * q->y + q->x * q->x));
            ox = eyePose[0].position.x;
            oy = eyePose[0].position.y;
            oz = eyePose[0].position.z;
            haveOrigin = 1;
        }
        if (g_recentre) { haveOrigin = 0; g_recentre = 0; }

        scale = 1.0f / g_unitsPerMetre;
        mIdent(model);
        model[0] = model[5] = model[10] = scale;
        mIdent(rot);
        rot[0] = cosf(originYaw);  rot[2]  = sinf(originYaw);
        rot[8] = -sinf(originYaw); rot[10] = cosf(originYaw);
        mIdent(t);
        t[3] = ox; t[7] = oy; t[11] = oz;
        mMul(rot, model, tmp);
        mMul(t, tmp, model);

        uploadVerts();
        uploadOverlay();
        uploadScreenTex();
        uploadAtlasTex();
        for (i = 0; i < 2; i++) {
            float view[16], proj[16], mvp[16], vp[16];
            float aH = atanf(aspect * tanf(fovY * 0.5f));
            mView(&eyePose[i], view);
            mProjFov(-aH, aH, fovY * 0.5f, -fovY * 0.5f, NEAR_M, FAR_M, proj);
            mMul(proj, view, vp);
            mMul(view, model, mvp);
            mMul(proj, mvp, mvp);
            g_vpX = (i == 0) ? 0.0f : (float)half;
            g_noClear = (i != 0);
            drawWith(rtv, dsv, half, H, mvp);
            drawUI(vp);
        }
        g_vpX = 0.0f; g_noClear = 0;
        IDXGISwapChain_Present(swap, 1, 0);

        wsprintfA(title, "VC2VR stereo - frame %u - %u tris - %d units/m - ipd %d mm",
                  g_lastFrame, g_localCount / 3, (int)g_unitsPerMetre,
                  (int)(ipd * 1000.0f));
        SetWindowTextA(hwnd, title);
    }
}

int main(int argc, char **argv)
{
    int wantWindow = 0, wantStereo = 0, i;
    for (i = 1; i < argc; i++) {
        if (!lstrcmpiA(argv[i], "--window")) wantWindow = 1;
        if (!lstrcmpiA(argv[i], "--stereo")) wantStereo = 1;
    }

    loadCfg();
    note("VC2VR - Virtua Cop 2 in a headset\n\n");
    note("waiting for the game...\n");
    for (i = 0; i < 600; i++) {
        if (openShare()) break;
        Sleep(500);
    }
    if (!g_frame)
        die("the game is not publishing anything.\n"
            "       Start Virtua Cop 2, choose \"Direct 3D + 3D view\" in Device Settings [F7],\n"
            "       and make sure share = 1 in HGL_VIEW.ini");
    note("connected to the game\n");

    if (wantStereo) return runStereo();
    return wantWindow ? runWindow() : runVR();
}
