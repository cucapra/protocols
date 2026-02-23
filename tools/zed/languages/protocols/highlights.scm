; ── Comments ──────────────────────────────────────────────────────────────────

(comment) @comment

; ── Annotations ───────────────────────────────────────────────────────────────

; #[idle]  →  highlight the whole annotation as an attribute
(annotation) @attribute

; ── Keywords ──────────────────────────────────────────────────────────────────

; Declaration keywords
"struct" @keyword.type
"prot"   @keyword.type

; Direction modifiers (in / out)
"in"  @keyword.modifier
"out" @keyword.modifier

; Control-flow keywords
"if"         @keyword.control
"else"       @keyword.control
"while"      @keyword.control
"repeat"     @keyword.control
"iterations" @keyword.control

; Built-in statement keywords (step, fork, assert_eq)
"step"      @function.builtin
"fork"      @function.builtin
"assert_eq" @function.builtin

; ── Types ─────────────────────────────────────────────────────────────────────

; u1, u8, u16, u32, u64, u128, …
(type) @type.builtin

; ── Named definitions ─────────────────────────────────────────────────────────

; struct Adder { … }  →  "Adder" is a type name
(struct_definition name: (path_id (identifier) @type))

; prot send_data<…>(…) { … }  →  "send_data" is a function name
(protocol_definition name: (path_id . (identifier) @function))

; ── Type parameters ───────────────────────────────────────────────────────────

; <DUT : Adder>  →  "DUT" is a parameter, "Adder" is a type
(type_param name: (path_id (identifier) @variable.parameter))
(type_param type: (path_id (identifier) @type))

; ── Argument / parameter declarations ────────────────────────────────────────

; in a : u32  →  "a" is a parameter name
(arg name: (path_id . (identifier) @variable.parameter))

; ── Expressions ───────────────────────────────────────────────────────────────

; Dotted paths:  DUT.a  →  "DUT" = variable,  "a" = member
; Must come before the general path_id rule so members take priority.
(path_id "." (identifier) @variable.member)
(path_id . (identifier) @variable)

; Don't-care wildcard: X
(wildcard) @constant.builtin

; Integers: width-prefixed (8'b1010) and plain decimal in step/slice positions
(integer_literal) @number
(dec_integer)     @number

; ── Operators ─────────────────────────────────────────────────────────────────

(not_op) @operator
":="     @operator
"=="     @operator
"+"      @operator

; ── Punctuation ───────────────────────────────────────────────────────────────

[ "{" "}" "(" ")" "[" "]" ] @punctuation.bracket
[ "," ";" ":" ]             @punctuation.delimiter
