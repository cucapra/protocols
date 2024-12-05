use pest::Parser;

#[derive(pest_derive::Parser)]
#[grammar = "protocols.pest"]
struct ProtocolParser;

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_file(filename: impl AsRef<std::path::Path>) {
        let input = std::fs::read_to_string(filename).expect("failed to load");
        let _ = ProtocolParser::parse(Rule::file, &input).expect("failed to parse");
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
