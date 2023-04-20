.PHONY: all

WEB_DIR = web
HTML_DIR = html
BIN = docs

FILE = NbE

CSS = $(WEB_DIR)/Custom.css
BOOTSTRAP = "https://cdn.jsdelivr.net/npm/bootstrap@4.0.0/dist/css/bootstrap.min.css"

all: $(BIN) $(BIN)/$(FILE).html
	agda --html $(FILE).lagda.md
	rm $(HTML_DIR)/$(FILE).html
	mv $(HTML_DIR)/* $(BIN)
	scp -r $(WEB_DIR)/ $(BIN)/

$(BIN):
	mkdir -p $(BIN)

$(BIN)/%.html:
	agda --html --html-highlight=code $*.lagda.md
	pandoc --standalone --embed-resources --css=$(BOOTSTRAP) --css=$(CSS) html/$*.md -o $(BIN)/$*.html

clean:
	rm -rf $(HTML_DIR)
	rm -rf $(BIN)
	rm -r *.agdai
