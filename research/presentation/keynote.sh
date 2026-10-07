#!/bin/sh
# Add the speaker notes in Keynote and write out/slides.key and out/slides.pptx.
# Run after make_pptx.py, from this folder.
# Usage: ./keynote.sh ["Keynote app name"]
set -e
app="${1:-Keynote}"
sed "s/__KEYNOTE__/$app/" keynote.applescript > build/keynote.applescript
osascript build/keynote.applescript "$PWD/build"
rm -rf out/slides.key
mv build/slides.key build/slides.pptx out/
echo "out/slides.key and out/slides.pptx written"
