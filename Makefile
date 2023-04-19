.PHONY: all

FILE = NbE
WEB_DIR = web
HTML_DIR = html
BIN = docs

all: $(BIN) $(BIN)/$(FILE).html
	agda --html $(FILE).lagda.md
	rm $(HTML_DIR)/$(FILE).html
	mv $(HTML_DIR)/* $(BIN)
	scp -r $(WEB_DIR)/ $(BIN)/

$(BIN):
	mkdir -p $(BIN)

$(BIN)/%.html:
	agda --html --html-highlight=code $*.lagda.md
	pandoc --standalone --embed-resources --css=html/Agda.css html/$*.md -o $(BIN)/$*.html

clean:
	rm -rf $(HTML_DIR)
	rm -rf $(BIN)
	rm -r *.agdai
