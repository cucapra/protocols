// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Graph-IR based reconstructor implementation.

// - build custom runner, we might want to generate results on the fly
// - we do not need to deal with the possibility of multiple traces
// - only support wellen inputs first, can add ascii wave support later
// - group transitions and actions by guard
// - can we save the guard evaluation history in order to decide which one to evaluate first?
// - is there maybe even a way to evaluate guards in parallel?
// - different than the existing bi, we should be able to never allocate during execution
// - we could define an array that contains all relevant values from the trace
//   and then compile expressions to byte code that contains the concrete indices
