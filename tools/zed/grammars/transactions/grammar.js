// Tree-sitter grammar for Protocols Transactions files (.tx files).
// Derived from protocols/src/transactions.pest.

module.exports = grammar({
  name: "transactions",

  extras: ($) => [/\s+/],

  word: ($) => $.identifier,

  rules: {
    source_file: ($) => repeat($._item),

    _item: ($) => choice($.directive_comment, $.comment, $.trace_block),

    // Directive comments: // ARGS: ... or // RETURN: ...
    // Given higher lexical precedence than plain comments so they are
    // preferred when both patterns could match.
    directive_comment: ($) =>
      token(prec(1, /\/\/\s*(ARGS|RETURN):.*/)),

    // Plain line comment: // ...
    comment: ($) => token(/\/.*/),

    // trace { transaction* }
    trace_block: ($) =>
      seq("trace", "{", repeat($._trace_item), "}"),

    _trace_item: ($) => choice($.comment, $.transaction),

    // ident ( arglist? ) ;
    transaction: ($) =>
      seq(
        field("function", $.identifier),
        "(",
        optional($.arg_list),
        ")",
        ";"
      ),

    // Comma-separated integer arguments (trailing comma allowed)
    arg_list: ($) =>
      seq(
        $.integer_literal,
        repeat(seq(",", $.integer_literal)),
        optional(",")
      ),

    // Integer literals: 0b..., 0x..., decimal
    integer_literal: ($) =>
      token(
        choice(
          /0[bB][01_]+/,
          /0[xX][0-9a-fA-F_]+/,
          /[0-9][0-9_]*/
        )
      ),

    identifier: ($) => /[a-zA-Z_][a-zA-Z0-9_]*/,
  },
});
