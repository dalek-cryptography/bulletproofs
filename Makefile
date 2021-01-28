FEATURES := yoloproofs

doc:
	cargo rustdoc --features "docs,$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html

doc-internal:
	cargo rustdoc --features "docs,$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html --document-private-items

