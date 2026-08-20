/*
 * vc2_share.h - the frame handoff between the 32-bit game and the 64-bit VR app.
 *
 * Virtua Cop 2 is a 1997 32-bit program; SteamVR is 64-bit. They cannot live in
 * one process, so the DLL inside the game only reconstructs geometry and drops
 * it into shared memory, and a separate 64-bit process picks it up and renders.
 * A crash on the VR side then cannot take the game down with it.
 *
 * Coordinates are already in OpenXR convention when they are written here:
 * X right, Y up, Z backwards (so the view direction is -Z), in game units.
 * Divide by units_per_metre to get metres.
 *
 * Synchronisation is a seqlock. The writer bumps seq to an odd value, writes,
 * then bumps it to the next even value. The reader takes seq, copies, takes seq
 * again, and retries if it changed or was odd. No locks, no blocking, and a
 * stalled reader can never stall the game.
 *
 * VERSION 4: vertices carry atlas UVs and the decoded texture atlas rides in
 * the mapping - the world is drawn with the game's real textures.
 *
 * VERSION 3: the screen capture is variable-sized (up to 1280x960) instead of
 * a fixed 640x480, so a dgVoodoo-upscaled window arrives at full quality.
 *
 * VERSION 2 added two things:
 *
 *   - the aim block is now actually used: the VR side writes where the
 *     controller points (in the game's own 640x480 screen space) plus button
 *     bits, and HGL_VIEW.DLL turns that into mouse and key input for the game.
 *
 *   - a capture of the game's own window (640x480 BGRA), written by the game
 *     side under its own seqlock. The VR side shows it on a floating screen,
 *     because menus, scores and cutscenes are drawn as 2D sprites that never
 *     pass through the quad slot - without this the headset shows an empty
 *     void everywhere outside actual gameplay.
 *
 * Both sides check the version. Do not mix a v1 binary with a v2 one: the
 * mapping sizes differ and the older side will fail to open or misread it.
 */

#ifndef VC2_SHARE_H
#define VC2_SHARE_H

#define VC2_SHARE_NAME    "Local\\VirtuaCop2_VR_Frame"
#define VC2_SHARE_MAGIC   0x32504356u      /* 'VCP2' */
#define VC2_SHARE_VERSION 8
#define VC2_MAX_VERTS     (40000 * 6)      /* the world cache holds a city */

/* the capture buffer holds up to this; the actual captured size travels in
 * screen_w / screen_h. 1280x960 = the game window with dgVoodoo's 2x
 * resolution forcing; anything larger is scaled down to fit. */
#define VC2_SCREEN_MAX_W  1280
#define VC2_SCREEN_MAX_H  960

/* v4: the texture atlas. The DLL decodes every slot +0x28 upload (8-bit
 * palettised, sizes in the table, pixels packed tight) into one BGRA sheet
 * and publishes it here under its own seqlock. Texture loads happen a handful
 * of times per session, so pushing the whole sheet each time is cheap. */
#define VC2_ATLAS_W       4096
#define VC2_ATLAS_H       4096

/* aim_buttons bits, VR -> game */
#define VC2_BTN_FIRE      1u               /* trigger: left mouse button      */
#define VC2_BTN_START     2u               /* A / X:   Enter                  */
#define VC2_BTN_BACK      4u               /* B / Y:   Escape                 */

#pragma pack(push, 4)

/* v4: u,v are atlas coordinates in 0..1, or u < 0 for "no texture, use the
 * colour as-is". For textured vertices the colour carries the game's shading
 * with 0x80 = neutral: the shader computes tex.rgb * colour.rgb * 2. */
typedef struct {
    float x, y, z;
    unsigned int colour;                   /* 0xAABBGGRR */
    float u, v;
    float depth;    /* v7: the engine's own depth key - the FULL 32-bit w
                     * (layer in the high bits) normalised to 0..1. The layer
                     * is part of the z-buffer in HGL_D3D (sz = K/w), which is
                     * how shadows sit on roads and sights float over all. */
} Vc2Vertex;

typedef struct {
    volatile unsigned int seq;             /* seqlock; odd means a write is in progress */
    unsigned int magic;
    unsigned int version;
    unsigned int frame;                    /* increments once per game frame */
    unsigned int vertex_count;
    float        fov_degrees;              /* the game's horizontal field of view */
    float        units_per_metre;
    unsigned int reserved[9];

    /* written by the VR side, read by the game side: where the controller is
     * pointing, in the game's own 640x480 screen space, for the light gun.
     * aim_seq increments after each update; the game side treats a stale
     * aim_seq as "the VR app is gone" and releases everything it held down. */
    volatile unsigned int aim_seq;
    float        aim_x, aim_y;
    unsigned int aim_buttons;

    /* capture of the game window, its own seqlock, writer = game side.
     * v3: the size is no longer fixed 640x480 - screen_w/screen_h say what was
     * actually captured, up to VC2_SCREEN_MAX_W x VC2_SCREEN_MAX_H. Rows are
     * tightly packed at screen_w pixels. */
    volatile unsigned int screen_seq;
    unsigned int screen_frame;
    unsigned int screen_ok;                /* 0 = capture failing, ignore pixels */
    unsigned int screen_w, screen_h;
    unsigned int screen_pad;

    volatile unsigned int atlas_seq;
    unsigned int atlas_frame;              /* bumps when the sheet changed */
    unsigned int atlas_pad[2];

    Vc2Vertex    verts[VC2_MAX_VERTS];
    unsigned int screen[VC2_SCREEN_MAX_W * VC2_SCREEN_MAX_H]; /* BGRA, top-down */
    unsigned int atlas[VC2_ATLAS_W * VC2_ATLAS_H];            /* BGRA */
} Vc2Frame;

#pragma pack(pop)

#endif
