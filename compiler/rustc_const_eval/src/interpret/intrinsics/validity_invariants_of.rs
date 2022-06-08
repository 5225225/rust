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

struct AbsolutePathPrinter<'tcx> {
    tcx: TyCtxt<'tcx>,
    path: String,
}

impl<'tcx> Printer<'tcx> for AbsolutePathPrinter<'tcx> {
    type Error = std::fmt::Error;

    type Path = Self;
    type Region = Self;
    type Type = Self;
    type DynExistential = Self;
    type Const = Self;

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn print_region(self, _region: ty::Region<'_>) -> Result<Self::Region, Self::Error> {
        Ok(self)
    }

    fn print_type(mut self, ty: Ty<'tcx>) -> Result<Self::Type, Self::Error> {
        match *ty.kind() {
            // Types without identity.
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Array(_, _)
            | ty::Slice(_)
            | ty::RawPtr(_)
            | ty::Ref(_, _, _)
            | ty::FnPtr(_)
            | ty::Never
            | ty::Tuple(_)
            | ty::Dynamic(_, _) => self.pretty_print_type(ty),

            // Placeholders (all printed as `_` to uniformize them).
            ty::Param(_) | ty::Bound(..) | ty::Placeholder(_) | ty::Infer(_) | ty::Error(_) => {
                write!(self, "_")?;
                Ok(self)
            }

            // Types with identity (print the module path).
            ty::Adt(ty::AdtDef(Interned(&ty::AdtDefData { did: def_id, .. }, _)), substs)
            | ty::FnDef(def_id, substs)
            | ty::Opaque(def_id, substs)
            | ty::Projection(ty::ProjectionTy { item_def_id: def_id, substs })
            | ty::Closure(def_id, substs)
            | ty::Generator(def_id, substs, _) => self.print_def_path(def_id, substs),
            ty::Foreign(def_id) => self.print_def_path(def_id, &[]),

            ty::GeneratorWitness(_) => bug!("type_name: unexpected `GeneratorWitness`"),
        }
    }

    fn print_const(self, ct: ty::Const<'tcx>) -> Result<Self::Const, Self::Error> {
        self.pretty_print_const(ct, false)
    }

    fn print_dyn_existential(
        mut self,
        predicates: &'tcx ty::List<ty::Binder<'tcx, ty::ExistentialPredicate<'tcx>>>,
    ) -> Result<Self::DynExistential, Self::Error> {
        let mut first = true;
        for p in predicates {
            if !first {
                write!(self, "+")?;
            }
            first = false;
            self = p.print(self)?;
        }
        Ok(self)
    }

    fn path_crate(mut self, cnum: CrateNum) -> Result<Self::Path, Self::Error> {
        self.path.push_str(self.tcx.crate_name(cnum).as_str());
        Ok(self)
    }

    fn path_qualified(
        self,
        self_ty: Ty<'tcx>,
        trait_ref: Option<ty::TraitRef<'tcx>>,
    ) -> Result<Self::Path, Self::Error> {
        self.pretty_path_qualified(self_ty, trait_ref)
    }

    fn path_append_impl(
        self,
        print_prefix: impl FnOnce(Self) -> Result<Self::Path, Self::Error>,
        _disambiguated_data: &DisambiguatedDefPathData,
        self_ty: Ty<'tcx>,
        trait_ref: Option<ty::TraitRef<'tcx>>,
    ) -> Result<Self::Path, Self::Error> {
        self.pretty_path_append_impl(
            |mut cx| {
                cx = print_prefix(cx)?;

                cx.path.push_str("::");

                Ok(cx)
            },
            self_ty,
            trait_ref,
        )
    }

    fn path_append(
        mut self,
        print_prefix: impl FnOnce(Self) -> Result<Self::Path, Self::Error>,
        disambiguated_data: &DisambiguatedDefPathData,
    ) -> Result<Self::Path, Self::Error> {
        self = print_prefix(self)?;

        write!(self.path, "::{}", disambiguated_data.data).unwrap();

        Ok(self)
    }

    fn path_generic_args(
        mut self,
        print_prefix: impl FnOnce(Self) -> Result<Self::Path, Self::Error>,
        args: &[GenericArg<'tcx>],
    ) -> Result<Self::Path, Self::Error> {
        self = print_prefix(self)?;
        let args =
            args.iter().cloned().filter(|arg| !matches!(arg.unpack(), GenericArgKind::Lifetime(_)));
        if args.clone().next().is_some() {
            self.generic_delimiters(|cx| cx.comma_sep(args))
        } else {
            Ok(self)
        }
    }
}

impl<'tcx> PrettyPrinter<'tcx> for AbsolutePathPrinter<'tcx> {
    fn should_print_region(&self, _region: ty::Region<'_>) -> bool {
        false
    }
    fn comma_sep<T>(mut self, mut elems: impl Iterator<Item = T>) -> Result<Self, Self::Error>
    where
        T: Print<'tcx, Self, Output = Self, Error = Self::Error>,
    {
        if let Some(first) = elems.next() {
            self = first.print(self)?;
            for elem in elems {
                self.path.push_str(", ");
                self = elem.print(self)?;
            }
        }
        Ok(self)
    }

    fn generic_delimiters(
        mut self,
        f: impl FnOnce(Self) -> Result<Self, Self::Error>,
    ) -> Result<Self, Self::Error> {
        write!(self, "<")?;

        self = f(self)?;

        write!(self, ">")?;

        Ok(self)
    }
}

impl Write for AbsolutePathPrinter<'_> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.path.push_str(s);
        Ok(())
    }
}

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

/// Directly returns an `Allocation` containing an absolute path representation of the given type.
pub(crate) fn alloc_type_name<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> ConstAllocation<'tcx> {
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
