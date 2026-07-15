use crate::{
    ctx::TranslationCtx,
    translation::pearlite::{MapSubstitution, Substable, Term, TermKind},
    util::erased_identity_for_item,
};
use itertools::{EitherOrBoth, Itertools};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{GenericArg, GenericArgsRef, TyCtxt};
use rustc_span::Span;
use rustc_type_ir::GenericArgKind;

pub(crate) fn get_logic_id(ctx: &TranslationCtx, def_id: DefId) -> DefId {
    let ensures_body = ctx.raw_term(def_id).expect("no ensures clause associated with this alias");

    match &ensures_body.1.kind {
        TermKind::Binary { rhs, .. } => match &rhs.kind {
            TermKind::Call { id, .. } => *id,
            _ => unreachable!("this should be a function call"),
        },
        _ => unreachable!("this should be an equality"),
    }
}

pub(crate) fn subst_call<'tcx, Args>(
    ctx: &TranslationCtx<'tcx>,
    prog_id: DefId,
    prog_args: Args,
) -> Option<(DefId, Box<[Term<'tcx>]>, GenericArgsRef<'tcx>)>
where
    Args: IntoIterator<Item = Term<'tcx>>,
{
    if let Some((_, alias_id)) = ctx.logic_alias(prog_id) {
        let ensures_body =
            ctx.raw_term(alias_id).expect("no ensures clause associated with this alias");
        match &ensures_body.1.kind {
            TermKind::Binary { rhs, .. } => match &rhs.kind {
                TermKind::Call { id, args, subst: call_subst } => {
                    let mut subst = MapSubstitution::new();

                    let prog_params = &ensures_body.0;
                    for (param, term) in
                        itertools::zip_eq(&prog_params[..prog_params.len() - 1], prog_args)
                    {
                        subst.insert(param.0, term.kind);
                    }

                    let helper_subst = |mut term: Term<'tcx>| {
                        term.subst(&subst);
                        term
                    };

                    let res_args = args.iter().map(|term| helper_subst(term.clone())).collect();
                    Some((*id, res_args, call_subst))
                }
                _ => unreachable!("this should be a function call"),
            },
            _ => unreachable!("this should be an equality"),
        }
    } else {
        None
    }
}

fn failwith(
    tcx: TyCtxt<'_>,
    msg: impl ToString,
    prog_span: Span,
    alias_span: Span,
    logic_span: Span,
) -> ! {
    tcx.dcx()
        .struct_span_err(alias_span, msg.to_string())
        .with_span_note(prog_span, "function defined here")
        .with_span_note(logic_span, "logic function defined here")
        .emit()
        .raise_fatal()
}

pub(crate) fn check_validity(
    ctx: &TranslationCtx,
    prog_id: DefId,
    alias_id: DefId,
    alias_span: Span,
) {
    let tcx = ctx.tcx;
    let logic_id = get_logic_id(ctx, alias_id);

    let prog_span = tcx.def_span(prog_id);
    let logic_span = tcx.def_span(logic_id);

    let prog_subst = erased_identity_for_item(tcx, prog_id);
    let logic_subst = erased_identity_for_item(tcx, logic_id);

    let from_trait = tcx.trait_item_of(prog_id).is_some();

    // The logic alias must come from the current crate.
    if !logic_id.is_local() {
        failwith(
            tcx,
            "The logic function must be defined in the same crate as the aliased program function.",
            prog_span,
            alias_span,
            logic_span,
        )
    }

    // A program function should only be aliased by a logic function
    // A trait method can either be aliased by a logic function or a logic method *from the same trait*
    match (tcx.assoc_parent(prog_id), tcx.assoc_parent(logic_id)) {
        (Some((id1, DefKind::Trait)), Some((id2, DefKind::Trait))) => {
            if id1 != id2 {
                failwith(
                    tcx,
                    format!(
                        "A trait method can only be aliased by a logic method from the same trait. \
                            (program method defined in trait {}, logic alias defined in trait {})",
                        tcx.def_path_str(id1),
                        tcx.def_path_str(id2),
                    ),
                    prog_span,
                    alias_span,
                    logic_span,
                )
            }
        }

        (Some((id1, DefKind::Impl { of_trait: true })), Some((id2, DefKind::Trait))) => {
            let trid = tcx.impl_trait_id(id1);

            if trid != id2 {
                failwith(
                    tcx,
                    format!(
                        "In an `impl T for ...` context, method can only be aliased by logic method in `T`. \
                            (program method defined for trait {}, logic alias defined in trait {})",
                        tcx.def_path_str(trid),
                        tcx.def_path_str(id2),
                    ),
                    prog_span,
                    alias_span,
                    logic_span,
                )
            }
        }

        (Some((_, DefKind::Trait)), Some((_, DefKind::Impl { .. }))) => failwith(
            tcx,
            "Aliasing trait method with non-trait method is incorrect",
            prog_span,
            alias_span,
            logic_span,
        ),

        (None, Some(_)) => failwith(
            tcx,
            "Aliasing a program function to a trait method is incorrect",
            prog_span,
            alias_span,
            logic_span,
        ),

        (_, _) => {}
    }

    if !from_trait {
        // program and logic functions must have the same generic arguments
        for arg in prog_subst
            .iter()
            .map(GenericArg::kind)
            .zip_longest(logic_subst.iter().map(GenericArg::kind))
        {
            use EitherOrBoth::*;

            match arg {
                Left(a) | Right(a) => {
                    let err = if arg.is_left() { "missing" } else { "additional" };

                    failwith(
                        tcx,
                        format!(
                            "mismatched generic parameters for #[logic_alias]: {err} parameter {a:?} in the alias"
                        ),
                        prog_span,
                        alias_span,
                        logic_span,
                    )
                }
                Both(GenericArgKind::Type(t1), GenericArgKind::Type(t2)) => {
                    if t1 != t2 {
                        failwith(
                            tcx,
                            format!("mismatched types in #[logic_alias]: expected {t1}, got {t2}"),
                            prog_span,
                            alias_span,
                            logic_span,
                        )
                    }
                }
                Both(GenericArgKind::Const(c1), GenericArgKind::Const(c2)) => {
                    let (pt, pname) = match c1.kind() {
                        rustc_type_ir::ConstKind::Param(p) => {
                            (p.find_const_ty_from_env(tcx.param_env(prog_id)), p.name)
                        }
                        _ => unreachable!(),
                    };

                    let (lt, lname) = match c2.kind() {
                        rustc_type_ir::ConstKind::Param(p) => {
                            (p.find_const_ty_from_env(tcx.param_env(logic_id)), p.name)
                        }
                        _ => unreachable!(),
                    };

                    if pt != lt || pname != lname {
                        failwith(
                            tcx,
                            format!(
                                "mismatched constants in #[logic_alias]: expected `{pname} : {pt}`, got `{lname} : {lt}`"
                            ),
                            prog_span,
                            alias_span,
                            logic_span,
                        )
                    }
                }
                Both(GenericArgKind::Lifetime(l1), GenericArgKind::Lifetime(l2)) => {
                    if l1 != l2 {
                        failwith(
                            tcx,
                            format!(
                                "mismatched lifetime parameters in #[logic_alias]: expected {l1}, got {l2}"
                            ),
                            prog_span,
                            alias_span,
                            logic_span,
                        )
                    }
                }
                Both(a1, a2) => failwith(
                    tcx,
                    format!(
                        "mismatched parameter kinds in #[logic_alias]: expected {a1:?}, got {a2:?}"
                    ),
                    prog_span,
                    alias_span,
                    logic_span,
                ),
            }
        }

        let bounds1 = tcx.param_env(prog_id).caller_bounds();
        let bounds2 = tcx.param_env(logic_id).caller_bounds();

        if bounds1 != bounds2 {
            let mut err =
                tcx.dcx().struct_span_err(alias_span, "mismatched trait bounds in #[logic_alias]");

            for (b1, b2) in bounds1.iter().rev().zip(bounds2.iter().rev()) {
                if b1 != b2 {
                    err.note(format!("{b1} != {b2}"));
                }
            }

            if bounds1.len() < bounds2.len() {
                for b in bounds2.iter().rev().skip(bounds1.len()) {
                    err.note(format!("additional bound {b} found"));
                }
            } else if bounds1.len() > bounds2.len() {
                for b in bounds1.iter().rev().skip(bounds2.len()) {
                    err.note(format!("missing bound {b}"));
                }
            }

            err.with_span_note(prog_span, "function defined here")
                .with_span_note(logic_span, "logic function defined here")
                .with_span_note(alias_span, "alias defined here")
                .emit()
                .raise_fatal()
        }
    }
}
