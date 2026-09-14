Expect: rejected. No `---- MODULE ... ----` header appears anywhere in this file, so
`Parser_/TLAPlus.lean`'s header-seeking lexer runs off the end of input still looking for one and
reports a lex error, rather than looping or crashing.
