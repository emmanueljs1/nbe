.PHONY: all

WEB_DIR = web
HTML_DIR = html
BIN = docs

FILE = NbE

REFERENCES = references.bib
CSS = $(WEB_DIR)/Custom.css
BOOTSTRAP = "https://cdn.jsdelivr.net/npm/bootstrap@4.0.0/dist/css/bootstrap.min.css"

all: $(BIN)/$(FILE).html
	# Generate HTML for imports
	agda --html $(FILE).lagda.md
	rm $(HTML_DIR)/$(FILE).html
	mv $(HTML_DIR)/* $(BIN)
	# Copy static web files
	scp -r $(WEB_DIR)/ $(BIN)/

# Generate main HTML page
$(BIN)/%.html: $(BIN) $(REFERENCES) $(CSS) $(HTML_DIR)/%.md
	pandoc --citeproc --bibliography $(REFERENCES) --standalone --embed-resources --css=$(BOOTSTRAP) --css=$(CSS) $(HTML_DIR)/$*.md -o $(BIN)/$*.html

$(BIN):
	mkdir -p $(BIN)

# Raw markdown from literate Agda
$(HTML_DIR)/%.md: %.lagda.md
	agda --html --html-highlight=code $*.lagda.md

clean:
	rm -rf $(HTML_DIR)
	rm -rf $(BIN)
	rm -r *.agdai
