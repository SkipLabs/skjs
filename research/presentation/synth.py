"""Synthesize build/<slide>.wav from narration.json with the Kokoro voice.

Run with the Kokoro environment's Python (see README.md), from this folder.
"""

import json
import os
import sys

os.environ["ESPEAK_DATA_PATH"] = "/opt/homebrew/share/espeak-ng-data"
from phonemizer.backend.espeak.wrapper import EspeakWrapper

EspeakWrapper.set_library("/opt/homebrew/lib/libespeak-ng.dylib")
EspeakWrapper.set_data_path("/opt/homebrew/share/espeak-ng-data")

import numpy as np
import soundfile as sf
from kokoro import KPipeline

import re

# Spoken spellings for words the voice mispronounces. Each written word is
# replaced before synthesis; longer words first, so "non-thenable" is matched
# before "thenable".
SPOKEN = {
    "non-thenables": "non then-uh-bulls",
    "non-thenable": "non then-uh-bull",
    "thenables": "then-uh-bulls",
    "thenable": "then-uh-bull",
}


def speakable(text):
    for written, spoken in SPOKEN.items():
        text = re.sub(rf"(?<![\w-]){re.escape(written)}(?![\w-])",
                      lambda m: spoken.capitalize() if m.group(0)[0].isupper() else spoken, text, flags=re.I)
    return text


voice = sys.argv[1] if len(sys.argv) > 1 else "af_heart"
narration = json.load(open("narration.json"))
os.makedirs("build", exist_ok=True)
pipeline = KPipeline(lang_code="a")
for sid, text in narration.items():
    chunks = [audio for _, _, audio in pipeline(speakable(text), voice=voice, speed=1.0)]
    sf.write(f"build/{sid}.wav", np.concatenate(chunks), 24000)
    print(sid, flush=True)
