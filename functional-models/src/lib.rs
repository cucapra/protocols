// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::system::TransitionSystem;
use serde::{Deserialize, Serialize};
use serde_json::Result;

#[derive(Debug)]
struct FunctionalModel {
    meta: FunctionalModelInfo,
    sys: TransitionSystem,
}

#[derive(Debug, Deserialize, Serialize)]
struct FunctionalModelJson {
    meta: FunctionalModelInfo,
    sys: String,
}

#[derive(Debug, Deserialize, Serialize)]
struct FunctionalModelInfo {
    name: String,
    transactions: Vec<Transaction>,
    states: Vec<String>,
}

#[derive(Debug, Deserialize, Serialize)]
struct Transaction {
    name: String,
}
