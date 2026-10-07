"""Assemble out/typing-promise-resolution.mp4 and out/narration.m4a from out/slides/*.png and build/<slide>.wav.

Each slide is shown for exactly its narration plus a lead-in and a tail. Each
slide's segment has a whole number of frames, taken from the running total, so
a transition is never more than one frame away from its narration.
"""

import json
import subprocess

LEAD, TAIL, RATE, FPS = 0.6, 1.0, 24000, 30


def run(*args):
    subprocess.run(["ffmpeg", "-y", "-loglevel", "error", *args], check=True)


order = json.load(open("deck/deck.json"))["order"]
total = 0.0
frames_done = 0
with open("build/segments.txt", "w") as segments, open("build/audio.txt", "w") as audio:
    for n, sid in enumerate(order, 1):
        spoken = float(subprocess.check_output(
            ["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", f"build/{sid}.wav"]))
        length = round((LEAD + spoken + TAIL) * RATE) / RATE
        run("-i", f"build/{sid}.wav", "-af", f"adelay={int(LEAD * 1000)}:all=1,apad", "-t", f"{length:.6f}",
            "-ar", str(RATE), "-ac", "1", f"build/{sid}.pad.wav")
        total += length
        frames = round(total * FPS) - frames_done
        frames_done += frames
        run("-loop", "1", "-framerate", str(FPS), "-i", f"out/slides/{n:02d}-{sid}.png", "-frames:v", str(frames),
            "-c:v", "libx264", "-tune", "stillimage", "-pix_fmt", "yuv420p", f"build/{sid}.mp4")
        segments.write(f"file '{sid}.mp4'\n")
        audio.write(f"file '{sid}.pad.wav'\n")
run("-f", "concat", "-safe", "0", "-i", "build/audio.txt", "-c:a", "pcm_s16le", "build/narration.wav")
run("-f", "concat", "-safe", "0", "-i", "build/segments.txt", "-c", "copy", "build/video.mp4")
run("-i", "build/video.mp4", "-i", "build/narration.wav", "-c:v", "copy", "-c:a", "aac", "-b:a", "192k",
    "out/typing-promise-resolution.mp4")
run("-i", "build/narration.wav", "-c:a", "aac", "-b:a", "160k", "out/narration.m4a")
probe = subprocess.check_output(["ffprobe", "-v", "error", "-count_frames", "-select_streams", "v",
                                 "-show_entries", "stream=nb_read_frames", "-of", "csv=p=0",
                                 "out/typing-promise-resolution.mp4"])
if int(probe) != frames_done:
    raise SystemExit(f"video has {int(probe)} frames, expected {frames_done}")
print(f"out/typing-promise-resolution.mp4: {total:.1f} s, {frames_done} frames")
