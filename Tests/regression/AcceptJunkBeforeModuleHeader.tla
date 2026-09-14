This is not TLA+ at all: an unterminated string ", stray symbols !@#$%^&*, and prose. Placed here
on purpose, as ordinary junk preceding the module header.
---- MODULE AcceptJunkBeforeModuleHeader ----
\* Expect: accepted. `Parser_/TLAPlus.lean`'s lexer used to tokenize the whole file up front, so
\* content before the header had to lex as valid TLA+ tokens -- the unterminated string two lines
\* up would abort the whole lex before the parser ever ran. The lexer now raw-skips everything
\* before the header instead of tokenizing it.

\* @type: Bool;
x == TRUE
====
