use crate::ir::meta_automaton::{MetaAutomaton, MetaOutcome, MetaState, PrePhase};

fn format_state(graph: &MetaAutomaton, state: &MetaState) -> String {
    let mut parts: Vec<String> = state
        .post_phase
        .iter()
        .map(|transaction| {
            format!(
                "{}<SUB>{}</SUB><SUP>({})</SUP>",
                escape_html(&graph.protocols[transaction.protocol].name),
                transaction.post_cycle,
                transaction.instance
            )
        })
        .collect();

    if let Some(frontier) = state.pre_phase {
        parts.push(match frontier {
            PrePhase::Choice { instance } => format!("E<SUP>({instance})</SUP>"),
            PrePhase::Pre {
                protocol,
                instance,
                elapsed,
            } => {
                format!(
                    "{}<SUB>pre[{}]</SUB><SUP>({})</SUP>",
                    escape_html(&graph.protocols[protocol].name),
                    elapsed,
                    instance
                )
            }
        });
    }

    if parts.is_empty() {
        "DONE".to_string()
    } else {
        parts.join(" ∧ ")
    }
}

fn escape_html(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

pub fn to_dot(graph: &MetaAutomaton) -> String {
    let mut output = String::from(
        "digraph \"driver_meta\" {\n  rankdir=LR;\n  node [shape=box];\n  entry [shape=plain,label=\"ENTRY\"];\n",
    );
    output.push_str(&format!("  entry -> node{};\n", graph.entry));

    for (node_id, node) in graph.nodes.iter().enumerate() {
        output.push_str(&format!(
            "  node{node_id} [label=<{}>];\n",
            format_state(graph, &node.state)
        ));
        for edge in &node.edges {
            let name = escape_html(&graph.protocols[edge.protocol].name);
            let mut label = match edge.outcome {
                MetaOutcome::Continue => format!("{name} continues"),
                MetaOutcome::Fork => format!("{name} forks"),
            };
            if !edge.rotations.is_empty() {
                let rotations = edge
                    .rotations
                    .iter()
                    .map(|rotation| {
                        let name = escape_html(&graph.protocols[rotation.protocol].name);
                        if rotation.amount == 1 {
                            format!("R<SUB>{name}</SUB>")
                        } else {
                            format!("R<SUB>{name}</SUB><SUP>{}</SUP>", rotation.amount)
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                label.push_str(&format!(" / {rotations}"));
            }
            output.push_str(&format!(
                "  node{node_id} -> node{} [label=<{}>];\n",
                edge.target, label
            ));
        }
    }
    output.push_str("}\n");
    output
}
