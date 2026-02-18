// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use pyo3::prelude::*;

#[pyfunction]
pub fn proto_test_fn() -> u64 {
    42
}

#[pymodule]
#[pyo3(name = "pyprotocols")]
fn protocols(_py: Python<'_>, m: &pyo3::Bound<'_, pyo3::types::PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(proto_test_fn, m)?)?;
    Ok(())
}
