//! `fixpt-heap` — values, the heap, the collector, and heap images.
//!
//! This is the bottom of the `fixpt` stack: the Scheme engine, both execution
//! engines, and the FX-87 and FX-91 front ends all sit on top of it. It owes
//! its shape to two requirements from the project brief:
//!
//! * **No reference counting.** References are word offsets into a flat array,
//!   so the collector is free to move objects and cycles cost nothing.
//! * **Heap dumping, decoupled *and* coupled.** A compacting collector means
//!   the live heap is already a contiguous, base-relative region, so writing an
//!   image is a copy and reading one needs no relocation pass at all.
//!
//! See [`heap`] for the allocation/collection invariant and [`image`] for the
//! three shipping modes.

pub mod heap;
pub mod image;
pub mod value;

pub use heap::Heap;
pub use image::ImageError;
pub use value::{ObjType, Value};
