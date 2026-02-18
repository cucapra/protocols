// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use pyo3::prelude::*;

#[pymodule]
#[pyo3(name = "protocols")]
fn protocols(_py: Python<'_>, m: &pyo3::Bound<'_, pyo3::types::PyModule>) -> PyResult<()> {
    Ok(())
}
