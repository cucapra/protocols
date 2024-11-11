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
    fn it_works() {
        parse_file("tests/add.prot")
    }
}
