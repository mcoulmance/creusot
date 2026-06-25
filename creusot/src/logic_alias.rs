use crate::{
    ctx::TranslationCtx,
    translation::pearlite::{MapSubstitution, Substable, Term, TermKind},
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::GenericArgsRef;

pub(crate) fn get_logic_id(ctx: &TranslationCtx, def_id: DefId) -> DefId {
    let ensures_body = ctx.term(def_id).expect("no ensures clause associated with this alias");

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
            ctx.term(alias_id).expect("no ensures clause associated with this alias");
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
