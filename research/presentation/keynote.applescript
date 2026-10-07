-- Open <dir>/images.pptx in Keynote, add one presenter note per slide from
-- <dir>/notes.txt, then save <dir>/slides.key and export <dir>/slides.pptx.
-- keynote.sh substitutes the Keynote application name for __KEYNOTE__.
on run argv
	set dir to item 1 of argv
	set src to (POSIX file (dir & "/images.pptx")) as alias
	set keyOut to POSIX file (dir & "/slides.key")
	set pptxOut to POSIX file (dir & "/slides.pptx")
	set noteLines to paragraphs of (read POSIX file (dir & "/notes.txt") as «class utf8»)
	with timeout of 600 seconds
		tell application "__KEYNOTE__"
			set d to open src
			if d is missing value then error "Keynote could not import images.pptx"
			repeat with i from 1 to count of slides of d
				set presenter notes of slide i of d to item i of noteLines
			end repeat
			save d in keyOut
			export d to pptxOut as Microsoft PowerPoint
			close d saving no
		end tell
	end timeout
	return "done"
end run
