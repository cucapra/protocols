// Tree-sitter grammar for the Protocols language (.prot files).
// Derived from protocols/src/protocols.pest.

module.exports = grammar({
  name: "protocols",

  // Comments and whitespace can appear anywhere between tokens.
  extras: ($) => [/\s+/, $.comment],

  // Declare `identifier` as the "word" token so that string literals
  // that match the identifier pattern (e.g. "struct", "X") are treated
  // as reserved keywords and take lexical precedence over identifiers.
  word: ($) => $.identifier,

  rules: {
    source_file: ($) => repeat($._item),

    _item: ($) => choice($.struct_definition, $.protocol_definition),

    // Line comment: // ...
    // The language only has line comments (no block comments).
    comment: ($) => token(seq("//", /.*/)),

    // Annotation: #[idle]
    annotation: ($) => seq("#[", field("name", $.identifier), "]"),

    // struct Name { arg, arg, ... }
    struct_definition: ($) =>
      seq(
        "struct",
        field("name", $.path_id),
        "{",
        optional($.arg_list),
        "}"
      ),

    // annotation? prot Name<TypeParam>(args) { body }
    protocol_definition: ($) =>
      seq(
        optional($.annotation),
        "prot",
        field("name", $.path_id),
        $.type_param,
        "(",
        optional($.arg_list),
        ")",
        field("body", $.block)
      ),

    // <name : Type>
    type_param: ($) =>
      seq(
        "<",
        field("name", $.path_id),
        ":",
        field("type", $.path_id),
        ">"
      ),

    // Comma-separated argument list (trailing comma allowed)
    arg_list: ($) => seq($.arg, repeat(seq(",", $.arg)), optional(",")),

    // dir name : type
    arg: ($) =>
      seq(
        field("direction", $.direction),
        field("name", $.path_id),
        ":",
        field("type", $.type)
      ),

    direction: ($) => choice("in", "out"),

    // { stmt* }
    block: ($) => seq("{", repeat($._statement), "}"),

    _statement: ($) =>
      choice(
        $.assignment_statement,
        $.step_statement,
        $.fork_statement,
        $.while_statement,
        $.repeat_statement,
        $.assert_statement,
        $.if_statement
      ),

    // path_id := expr ;
    assignment_statement: ($) =>
      seq(field("target", $.path_id), ":=", field("value", $._expression), ";"),

    // step ( dec_integer? ) ;
    step_statement: ($) =>
      seq("step", "(", optional($.dec_integer), ")", ";"),

    // fork () ;
    fork_statement: ($) => seq("fork", "(", ")", ";"),

    // while expr { stmt* }
    // No parentheses around condition — parens come from paren_expression if written.
    while_statement: ($) =>
      seq(
        "while",
        field("condition", $._expression),
        field("body", $.block)
      ),

    // repeat expr iterations { stmt* }
    repeat_statement: ($) =>
      seq(
        "repeat",
        field("count", $._expression),
        "iterations",
        field("body", $.block)
      ),

    // assert_eq ( expr , expr ) ;
    assert_statement: ($) =>
      seq(
        "assert_eq",
        "(",
        field("left", $._expression),
        ",",
        field("right", $._expression),
        ")",
        ";"
      ),

    // if expr { stmt* } (else { stmt* })?
    if_statement: ($) =>
      seq(
        "if",
        field("condition", $._expression),
        field("consequence", $.block),
        optional(seq("else", field("alternative", $.block)))
      ),

    // ── Expressions ──────────────────────────────────────────────────────────

    _expression: ($) =>
      choice(
        $.binary_expression,
        $.unary_expression,
        $.slice_expression,
        $.paren_expression,
        $.integer_literal,
        $.wildcard,
        $.path_id
      ),

    // atom == atom  (prec 2)
    // atom +  atom  (prec 1)
    binary_expression: ($) =>
      choice(
        prec.left(
          2,
          seq(
            field("left", $._expression),
            "==",
            field("right", $._expression)
          )
        ),
        prec.left(
          1,
          seq(
            field("left", $._expression),
            "+",
            field("right", $._expression)
          )
        )
      ),

    // ! expr
    unary_expression: ($) =>
      prec(3, seq(field("operator", $.not_op), field("operand", $._expression))),

    not_op: ($) => "!",

    // path_id [ high : low ]  or  path_id [ index ]
    slice_expression: ($) =>
      seq(
        field("base", $.path_id),
        "[",
        field("high", $.dec_integer),
        optional(seq(":", field("low", $.dec_integer))),
        "]"
      ),

    // ( expr )
    paren_expression: ($) => seq("(", $._expression, ")"),

    // Don't-care wildcard: X
    wildcard: ($) => token("X"),

    // ── Terminals ─────────────────────────────────────────────────────────────

    // Built-in type: u<digits>  e.g. u1, u8, u32, u128
    type: ($) => /u[0-9]+/,

    // Dotted path: a.b.c
    path_id: ($) => seq($.identifier, repeat(seq(".", $.identifier))),

    // Width-prefixed integer: width'base digits
    //   e.g.  8'b1010_1010  16'hDEAD  32'd42  8'o77
    integer_literal: ($) =>
      token(
        choice(
          /[0-9][0-9_]*'[bB][01_]+/,
          /[0-9][0-9_]*'[oO][0-7_]+/,
          /[0-9][0-9_]*'[xX][0-9a-fA-F_]+/,
          /[0-9][0-9_]*'[dD][0-9_]+/
        )
      ),

    // Plain decimal integer (used in step() argument and slice indices)
    dec_integer: ($) => /[0-9][0-9_]*/,

    identifier: ($) => /[a-zA-Z_][a-zA-Z0-9_]*/,
  },
});
