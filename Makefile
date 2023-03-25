.PHONY: all

SINKFILE = Soundness.lagda.md

SRCFILES = SystemT.lagda.md NbE.lagda.md Soundness.lagda.md
HTMLS = $(patsubst %.lagda.md, %.html, $(SRCFILES))
HTML_DIR = html
BIN = web


all: $(BIN) $(patsubst %, $(BIN)/%, $(HTMLS))
	agda --html $(SINKFILE)
	rm $(patsubst %, $(HTML_DIR)/%, $(HTMLS))
	mv $(HTML_DIR)/* $(BIN)

$(BIN):
	mkdir -p $(BIN)

$(BIN)/%.html:
	agda --html --html-highlight=code $*.lagda.md
	pandoc --standalone --embed-resources --css=html/Agda.css html/$*.md -o $(BIN)/$*.html

clean:
	rm -rf html/
	rm -r *.agdai
