// run-pass
// needs-unwind
// ignore-wasm32-bare compiled with panic=abort by default
//
// this test tests that validity_invariants_of works fine
#![feature(core_intrinsics)]

#[repr(C)]
struct Complex {
    a: char,
    b: bool,
    c: std::num::NonZeroI32,
}

#[allow(invalid_value, unreachable_code)]
fn main() {
    let _c = std::mem::MaybeUninit::<Complex>::zeroed();
    eprintln!("oh\n\n\n--------");
    eprintln!("{:#?}", core::intrinsics::validity_invariants_of::<Complex>());
    eprintln!("\n\n\n------no");
    // core::intrinsics::assert_validity_of(c.as_ptr());
//        c.assume_init();
//    panic!();
  unsafe {
    let _c = std::mem::MaybeUninit::<Complex>::zeroed().assume_init();
}
}
