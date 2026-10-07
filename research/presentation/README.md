# Typing Promise Resolution: slides and narrated video

A 14-slide talk summarising [promise-normalization.md](../promise-normalization.md) and [promise-coverage-audit.md](../promise-coverage-audit.md), and a narrated video of it.

| File | Contents |
| --- | --- |
| `deck/deck.json`, `deck/slides/*.html` | The deck in the Slides artifact format: index, then one `<section>` per slide with its speaker notes. Published at <https://claude.ai/artifact/JnZQTaJc7gNJVBUArqSmUX> (private). |
| `narration.json` | The spoken text, one entry per slide id. |
| `render.py` | Renders each slide to `out/slides/NN-<id>.png` with headless Chrome, and joins them into `out/slides.pdf`. |
| `synth.py` | Speaks `narration.json` into `build/<id>.wav` with the Kokoro voice `af_heart`. |
| `build_video.py` | Assembles `out/typing-promise-resolution.mp4`, each slide timed to its narration, and `out/narration.m4a`. |
| `make_pptx.py` | Writes the slide images and the speaker notes for `keynote.sh`. |
| `keynote.sh`, `keynote.applescript` | Has Keynote add the speaker notes, save `out/slides.key` and export `out/slides.pptx`. |
| `out/slides/*.png`, `out/slides.pdf` | The rendered slides, 1920×1080. |
| `out/slides.key`, `out/slides.pptx` | The deck for Keynote and PowerPoint: one full-slide image per slide, with the speaker notes. |
| `out/narration.m4a` | The narration soundtrack alone. |
| `out/typing-promise-resolution.mp4` | The narrated video, 1080p, 6 min 41 s. |

## Rebuilding

Requirements: Google Chrome, Keynote, `ffmpeg`, `brew install espeak-ng`, and `uv`.

```bash
uv venv --python 3.12 .venv
```

```bash
uv pip install --python .venv/bin/python "kokoro>=0.9.4" "transformers>=4.44" "misaki[en]>=0.9.4" soundfile python-pptx
```

```bash
python3 render.py && VIRTUAL_ENV=$PWD/.venv PATH=$PWD/.venv/bin:$PATH python synth.py && python3 build_video.py
```

```bash
.venv/bin/python make_pptx.py && ./keynote.sh
```

`render.py` also needs Pillow (`pip install pillow`). The first `synth.py` run downloads the Kokoro model and the spaCy English model. `keynote.sh` takes the Keynote application's name when it is not `Keynote`, for example `./keynote.sh "Keynote Creator Studio"`; macOS asks once to allow controlling it. `.venv/` and `build/` hold intermediate files; `out/` holds the outputs.
