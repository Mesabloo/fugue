---- MODULE AcceptJunkAfterModuleFooter ----
\* Expect: accepted. `Parser_/TLAPlus.lean`'s parser used to require `endOfInput` right after the
\* `.moduleEnd` token, so anything trailing the footer had to be absent. The lexer now stops
\* tokenizing at `.moduleEnd` and drops the remainder unread -- proven below by trailing content
\* that is not even valid TLA+ tokens (an unterminated string, stray symbols).

\* @type: Bool;
x == TRUE
====
This is not TLA+ at all: an unterminated string ", stray symbols !@#$%^&*, and prose. Placed here
on purpose, as ordinary junk following the module footer.
