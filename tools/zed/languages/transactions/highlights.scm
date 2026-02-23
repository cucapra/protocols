; ── Comments ──────────────────────────────────────────────────────────────────

; Directive comment lines: // ARGS: ...  or  // RETURN: ...
; Highlighted as a keyword so they stand out from plain comments.
(directive_comment) @keyword.control

; Plain comment: // ...
(comment) @comment

; ── Keywords ──────────────────────────────────────────────────────────────────

"trace" @keyword.control

; ── Transactions ──────────────────────────────────────────────────────────────

; Function name in a transaction call
(transaction function: (identifier) @function.call)

; ── Literals ──────────────────────────────────────────────────────────────────

(integer_literal) @number

; ── Punctuation ───────────────────────────────────────────────────────────────

[ "{" "}" "(" ")" ] @punctuation.bracket
[ "," ";" ]         @punctuation.delimiter
