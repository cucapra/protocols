use pest::Parser;
use std::fmt;
use pest::error::Error;

#[derive(pest_derive::Parser)]
#[grammar = "protocols.pest"]
struct ProtocolParser;

// Wrapper struct for custom display of pest pairs
struct DisplayPair<'i, R: pest::RuleType>(pest::iterators::Pair<'i, R>);

impl<'i, R: pest::RuleType> fmt::Display for DisplayPair<'i, R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.display(f, 0)
    }
}

impl<'i, R: pest::RuleType> DisplayPair<'i, R> {
    fn display(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        let rule = self.0.as_rule();
        let span = self.0.clone().as_span();
        let text = self.0.clone().as_str();
        let indent = "  ".repeat(depth);

        // Display the rule and token matched
        if self.0.clone().into_inner().count() == 0 {
            // Leaf node (no inner rules)
            writeln!(f, "{}- {:?}: \"{}\"", indent, rule, text)?;
        } else {
            // Non-leaf node with children
            writeln!(f, "{}- {:?}", indent, rule)?;
            for pair in self.0.clone().into_inner() {
                DisplayPair(pair).display(f, depth + 1)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_file(filename: impl AsRef<std::path::Path>) {
        let input = std::fs::read_to_string(filename).expect("failed to load");
    
        match ProtocolParser::parse(Rule::file, &input) {
            Ok(parsed) => println!("Parsing successful: {:?}", parsed),
            Err(err) => {
                eprintln!("Parsing failed: {}", err);
                panic!("failed to parse");
            }

        }
    }

    #[test]
    fn test_add_prot() {
        parse_file("tests/add.prot");
    }

    #[test]
    fn test_calyx_go_done_prot() {
        parse_file("tests/calyx_go_done.prot");
    }

    #[test]
    fn test_mul_prot() {
        parse_file("tests/mul.prot");
    }

    #[test]
    fn test_cond_prot() {
        parse_file("tests/cond.prot");
    }
}
