use pest::Parser;

#[derive(pest_derive::Parser)]
#[grammar = "protocols.pest"]
struct ProtocolParser;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let a = ProtocolParser::parse(Rule::id, "test")
            .expect("failed to parse")
            .next()
            .unwrap();
        let name = a.as_str().to_string();
        let b = ProtocolParser::parse(Rule::id, "test.a 543")
            .expect("failed to parse")
            .next()
            .unwrap();
    }
}
