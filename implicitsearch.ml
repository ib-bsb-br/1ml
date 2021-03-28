open Types
open Sub
open Source

module EL = Syntax

type implicit_tree = { parent : implicit_tree option ref; v: var; t: typ; aks : (var * kind) list }

let current_parent = ref None

let register_impl_bind v t aks = current_parent := Some { parent = ref !current_parent; v = v; t = t; aks = aks }

let remove_last_impl_bind () = current_parent := match !current_parent with 
  | Some node -> !(node.parent)
  | None -> assert false

let rec impl_candidates tree = match tree with 
  | Some node -> (node.v, node.t, node.aks) :: (impl_candidates !(node.parent))
  | None -> []

type implicit = {v : var; t : typ; aks: (var * kind) list; zs : infer ref list; tvar : typ; node : implicit_tree option }

let unresolved_impls = ref []

let create_implicit v t aks zs tvar = {v = v; t = t; aks = aks; zs = zs; tvar = tvar; node = !current_parent}

let rec expand_function = function 
  | FunT(aks1, t1, ExT([], t2), ImplicitModule) -> 
    let args, res, aks2 = expand_function t2 in t1 :: args, res, aks1 @ aks2
  | x -> ([], x, [])

let rec infer_helper c def = match !c with | Det (InferT c') -> infer_helper c' def | Det t -> t | _ -> def

let rec implicit_search env aks1 t1 zs node = 
  List.filter_map(fun (v, cand, aks') ->
  let env = Env.add_typs aks' env in
  let ts', zs' = guess_typs (Env.domain_typ env) aks1 in
  let t1'' = subst_typ 
    (List.map (fun ((a, b), c) -> (a, infer_helper c b))
    (List.combine (List.combine (List.map fst aks1) ts') zs)) t1 in
  match cand with 
  | FunT(_, _, _, ImplicitModule) -> 
    let argTs, resT, aks2 = expand_function cand in
    let ts2, zs2 = guess_typs (Env.domain_typ env) aks2 in
    let argTs = List.map (subst_typ (subst aks2 ts2)) argTs in
    let resT = (subst_typ (subst aks2 ts2) resT) in
    let sub = try Some (sub_typ env resT t1'' (varTs aks2)) with Sub _ -> None in
    let term = List.fold_left (fun e argT -> 
    Option.bind e (fun (e, env') -> 
    (match sub with
    | None -> None
    | _ -> let candidates = implicit_search env aks2 argT zs2 node in
      let term, _, env' = List.hd candidates in
      if (List.length candidates = 1) then (Some (EL.asVarE(EL.ModuleArgE(term)@@nowhere_region, fun k -> 
                                                  EL.asVarE(e, fun f -> 
                                                    EL.AppE(f, k, EL.Expl@@nowhere_region)@@nowhere_region)@@nowhere_region)@@nowhere_region, env')) else None))) 
      (Some (EL.VarE(v@@nowhere_region)@@nowhere_region, Env.empty)) argTs in
    Option.map (fun (e, env') -> (e, resT, if not (Env.mem_val v env') then Env.add_val v cand (Env.add_typs aks' env') else env')) term
  | _ ->
    try sub_typ env cand t1'' (varTs aks1); 
      Some ((EL.VarE (v@@nowhere_region))@@nowhere_region, cand, Env.add_val v cand env) with Sub _ -> None) 
      (impl_candidates node)

let resolve_implicits env impls = List.map (fun i ->
  match implicit_search env i.aks i.t i.zs i.node with 
  | [] -> error nowhere_region "implicit resolve failed: none matching"
  | [(e, t', env')] ->  let _, _, f = sub_typ env t' i.tvar (varTs i.aks) in (i.v, e, f, env')
  | res -> error nowhere_region "implicit resolve failed: ambiguity"
) impls

(* TODO: think about shadowing implicits*)
let rec dummy_subst s e = 
match e with
| IL.VarE(x) -> (try List.assoc x s with Not_found -> e)
| IL.PrimE(_) -> e
| IL.IfE(e1, e2, e3) ->
  let e1' = dummy_subst s e1 in
  let e2' = dummy_subst s e2 in
  let e3' = dummy_subst s e3 in
  if e1 == e1' && e2 == e2' && e3 == e3' then e else IL.IfE(e1', e2', e3')
| IL.LamE(x, t, e1) ->
  let e1' = dummy_subst s e1 in
  if e1 == e1' then e else LamE(x, t, e1')
| IL.AppE(e1, e2) ->
  let e1' = dummy_subst s e1 in
  let e2' = dummy_subst s e2 in
  if e1 == e1' && e2 == e2' then e else IL.AppE(e1', e2')
| IL.TupE(er) ->
  let er' = IL.subst_row dummy_subst s er in
  if er == er' then e else IL.TupE(er')
| IL.DotE(e1, l) ->
  let e1' = dummy_subst s e1 in
  if e1 == e1' then e else IL.DotE(e1', l)
| IL.GenE(a, k, e1) ->
  let e1' = dummy_subst s e1 in
  if e1 == e1' then e else IL.GenE(a, k, e1')
| IL.InstE(e1, t) ->
  let e1' = dummy_subst s e1 in
  if e1 == e1' then e else IL.InstE(e1', t)
| IL.PackE(t1, e1, t) ->
  let e1' = dummy_subst s e1 in
  if e1 == e1' then e else IL.PackE(t1, e1', t)
| IL.OpenE(e1, a, x, e2) ->
  let e1' = dummy_subst s e1 in
  let e2' = dummy_subst s e2 in
  if e1 == e1' && e2 == e2' then e else IL.OpenE(e1', a, x, e2')
| IL.RollE(e1, t) ->
  let e1' = dummy_subst s e1 in
  if e1 == e1' then e else IL.RollE(e1', t)
| IL.UnrollE(e1) ->
  let e1' = dummy_subst s e1 in
  if e1 == e1' then e else IL.UnrollE(e1')
| IL.RecE(x, t, e1) ->
  let e1' = dummy_subst s e1 in
  if e1 == e1' then e else IL.RecE(x, t, e1')
| IL.LetE(e1, x, e2) ->
  let e1' = dummy_subst s e1 in
  let e2' = dummy_subst s e2 in
  if e1 == e1' && e2 == e2' then e else IL.LetE(e1', x, e2')

let filter_out_implicit_related = List.filter (fun z -> match !z with | Undet u ->
  not (List.exists (fun i -> occurs_typ u i.tvar) !unresolved_impls))