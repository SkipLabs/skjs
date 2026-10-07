"""Render each slide of deck/ to out/slides/NN-<slide>.png (1920x1080) and out/slides.pdf.

The page wrapper approximates the Slides artifact runtime: same fonts and
inline styles, speaker notes dropped.
"""

import json
import os
import re
import subprocess

from PIL import Image

CHROME = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"

deck = json.load(open("deck/deck.json"))
fonts = next(iter(deck["faces"].values()))["href"]
os.makedirs("build", exist_ok=True)
os.makedirs("out/slides", exist_ok=True)
for old in os.listdir("out/slides"):
    os.remove(f"out/slides/{old}")
pngs = []
for n, sid in enumerate(deck["order"], 1):
    section = re.sub(r"<aside>.*?</aside>", "", open(f"deck/slides/{sid}.html").read(), flags=re.S)
    page = (
        f'<!doctype html><html><head><meta charset="utf-8"><link rel="stylesheet" href="{fonts}">'
        "<style>*{box-sizing:border-box;margin:0} body{width:1920px;height:1080px;overflow:hidden}"
        " section{width:1920px;height:1080px;position:relative} ul,ol{padding-left:1.2em} hr{border:none}</style>"
        f"</head><body>{section}</body></html>"
    )
    html = os.path.abspath(f"build/{sid}.html")
    png = f"out/slides/{n:02d}-{sid}.png"
    pngs.append(png)
    open(html, "w").write(page)
    subprocess.run(
        [CHROME, "--headless=new", "--disable-gpu", "--hide-scrollbars", "--window-size=1920,1080",
         "--virtual-time-budget=4000", f"--screenshot={os.path.abspath(png)}", f"file://{html}"],
        check=True, capture_output=True)
    print(sid, flush=True)
images = [Image.open(p).convert("RGB") for p in pngs]
images[0].save("out/slides.pdf", save_all=True, append_images=images[1:], resolution=144)
