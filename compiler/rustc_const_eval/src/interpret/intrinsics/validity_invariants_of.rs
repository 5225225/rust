use rustc_middle::mir::interpret::{Allocation, ConstAllocation};
use rustc_middle::mir::Mutability;
use rustc_middle::ty::layout::LayoutCx;
use rustc_middle::ty::{ParamEnv, ParamEnvAnd};
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_target::abi::{Abi, Align, Endian, FieldsShape, HasDataLayout, Scalar, WrappingRange};

#[derive(Debug, Clone, Copy)]
struct Invariant {
    offset: Size,
    size: Size,
    start: u128,
    end: u128,
}

use rustc_target::abi::Size;

fn add_invariants<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, invs: &mut Vec<Invariant>, offset: Size) {
    let x = tcx.layout_of(ParamEnvAnd { param_env: ParamEnv::reveal_all(), value: ty });

    if let Ok(layout) = x {
        if let Abi::Scalar(Scalar::Initialized { value, valid_range }) = layout.layout.abi() {
            let size = value.size(&tcx);
            let WrappingRange { start, end } = valid_range;
            invs.push(Invariant { offset, size, start, end })
        }

        let param_env = ParamEnv::reveal_all();
        let unwrap = LayoutCx { tcx, param_env };

        match layout.layout.fields() {
            FieldsShape::Primitive => {}
            FieldsShape::Union(_) => {}
            FieldsShape::Array { stride, count } => {
                for idx in 0..*count {
                    let off = offset + *stride * idx;
                    let f = layout.field(&unwrap, idx as usize);
                    add_invariants(tcx, f.ty, invs, off);
                }
            }
            FieldsShape::Arbitrary { offsets, .. } => {
                for (idx, &field_offset) in offsets.iter().enumerate() {
                    let f = layout.field(&unwrap, idx);
                    if f.ty == ty {
                        // Some types contain themselves as fields, such as
                        // &mut [T]
                        // Easy solution is to just not recurse then.
                    } else {
                        add_invariants(tcx, f.ty, invs, offset + field_offset);
                    }
                }
            }
        }
    }
}

/// Directly returns an `Allocation` containing a list of validity invariants of the given type.
pub(crate) fn alloc_validity_invariants_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
) -> ConstAllocation<'tcx> {
    let mut invs: Vec<Invariant> = Vec::new();

    add_invariants(tcx, ty, &mut invs, Size::ZERO);

    let mut path = Vec::new();

    let layout = tcx.data_layout();

    let encode_size = match (layout.endian, layout.pointer_size.bits()) {
        (Endian::Little, 16) => {
            |s: Size, path: &mut Vec<u8>| path.extend((s.bytes() as u16).to_le_bytes())
        }
        (Endian::Little, 32) => {
            |s: Size, path: &mut Vec<u8>| path.extend((s.bytes() as u32).to_le_bytes())
        }
        (Endian::Little, 64) => {
            |s: Size, path: &mut Vec<u8>| path.extend((s.bytes()).to_le_bytes())
        }
        (Endian::Big, 16) => {
            |s: Size, path: &mut Vec<u8>| path.extend((s.bytes() as u16).to_be_bytes())
        }
        (Endian::Big, 32) => {
            |s: Size, path: &mut Vec<u8>| path.extend((s.bytes() as u32).to_be_bytes())
        }
        (Endian::Big, 64) => |s: Size, path: &mut Vec<u8>| path.extend((s.bytes()).to_be_bytes()),
        _ => panic!("Unexpected pointer size"),
    };

    let encode_range = match layout.endian {
        Endian::Little => |r: u128| r.to_le_bytes(),
        Endian::Big => |r: u128| r.to_be_bytes(),
    };

    for inv in invs {
        encode_size(inv.offset, &mut path);
        encode_size(inv.size, &mut path);
        path.extend(encode_range(inv.start));
        path.extend(encode_range(inv.end));
    }

    let alloc = Allocation::from_bytes(path, Align::from_bytes(8).unwrap(), Mutability::Not);
    tcx.intern_const_alloc(alloc)
}
