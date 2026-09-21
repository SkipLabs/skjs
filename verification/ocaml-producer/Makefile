OCAMLC ?= ocamlc
MODULES = json semantic environment source proposal claims producer
SOURCES = $(addsuffix .ml,$(MODULES))
OBJECTS = $(addprefix _build/,$(addsuffix .cmo,$(MODULES)))
.PHONY: all clean test
all: _build/producer
_build/producer: $(SOURCES)
	mkdir -p _build
	@set -e; for m in $(MODULES); do $(OCAMLC) -w +a-4-42-45-70 -warn-error +8 -I _build -c -o _build/$$m.cmo $$m.ml; done
	$(OCAMLC) -I _build -o $@ $(OBJECTS)
_build/unit: _build/producer unit.ml
	$(OCAMLC) -I _build -c -o _build/unit.cmo unit.ml
	$(OCAMLC) -I _build -o $@ _build/json.cmo _build/semantic.cmo _build/unit.cmo
test: all _build/unit
	./_build/unit
	node test.mts
clean:
	rm -rf _build
