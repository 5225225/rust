use rustc_data_structures::intern::Interned;
use rustc_hir::def_id::CrateNum;
use rustc_hir::definitions::DisambiguatedDefPathData;
use rustc_middle::mir::interpret::{Allocation, ConstAllocation};
use rustc_middle::ty::{
    self,
    print::{PrettyPrinter, Print, Printer},
    subst::{GenericArg, GenericArgKind},
    Ty, TyCtxt,
};
use std::fmt::Write;

#[derive(Debug, Clone, Copy)]
struct Invariant {
    offset: Size,
    size: Size,
    start: u128,
    end: u128,
}

use rustc_target::abi::Size;

fn add_invariants<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, invs: &mut Vec<Invariant>, offset: Size, depth: usize) {
    if depth == 0 { return; }

    use rustc_middle::mir::Mutability;
    use rustc_middle::ty::{ParamEnv, ParamEnvAnd};
    use rustc_target::abi::{Abi, Align, Scalar, WrappingRange, FieldsShape};
    use rustc_middle::ty::layout::LayoutCx;
    use rustc_target::abi::TyAndLayout;

    let x = tcx.layout_of(ParamEnvAnd { param_env: ParamEnv::reveal_all(), value: ty });

    if let Ok(layout) = x {
        if let Abi::Scalar(Scalar::Initialized { value, valid_range }) = layout.layout.abi() {
            let size = value.size(&tcx);
            let WrappingRange { start, end } = valid_range;
            invs.push(Invariant { offset, size, start, end })
        }

        let fields = layout.layout.fields();

        let param_env = ParamEnv::reveal_all();
        let unwrap = LayoutCx { tcx, param_env };

        match layout.layout.fields() {
            FieldsShape::Primitive => {},
            FieldsShape::Union(_) => {},
            FieldsShape::Array{ .. } => {
                // TODO: We *could* check arrays, but do that as future work.
            },
            FieldsShape::Arbitrary { offsets, memory_index } => {
                for (idx, &field_offset) in offsets.iter().enumerate() {
                    let f = layout.field(&unwrap, idx);
                    add_invariants(tcx, f.ty, invs, offset+field_offset, depth - 1)
                }
            }
        }
    }
}

/// Directly returns an `Allocation` containing a list of validity invariants of the given type.
pub(crate) fn alloc_validity_invariants_of<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> ConstAllocation<'tcx> {
    use rustc_middle::mir::Mutability;
    use rustc_middle::ty::{ParamEnv, ParamEnvAnd};
    use rustc_target::abi::{Abi, Align, Scalar, WrappingRange};
    use rustc_middle::ty::layout::LayoutCx;
    use rustc_target::abi::TyAndLayout;

    let mut invs: Vec<Invariant> = Vec::new();

    add_invariants(tcx, ty, &mut invs, Size::ZERO, 3);

    let mut path = Vec::new();

    for inv in invs {
        path.extend(inv.offset.bytes().to_le_bytes());
        path.extend(inv.size.bytes().to_le_bytes());
        path.extend(inv.start.to_le_bytes());
        path.extend(inv.end.to_le_bytes());
    }

    let alloc = Allocation::from_bytes(path, Align::from_bytes(8).unwrap(), Mutability::Not);
    tcx.intern_const_alloc(alloc)
}
