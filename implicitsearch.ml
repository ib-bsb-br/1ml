open Types
open Source
open Either

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
  | FunT(aks1, t1, res, ImplicitModule) -> [t1], res, aks1
  | x -> ([], ExT([], x), [])

let rec infer_helper c def = match !c with | Det (InferT c') -> infer_helper c' def | Det t -> t | _ -> def

module SMap = Map.Make(String)
module PSet = Set.Make(struct type t = int * string let compare = Stdlib.compare end)

type search_local_state = {
  curr_cs : typ list;
  cs_history : (typ list) SMap.t
}
type cmp = Gt | Less | Eq | NotCmp

let cmp_typs t1 t2 = if t1 = t2 then Eq else Less

let constrainsts_smaller cs1 cs2 = 
  let cmps = List.map2 cmp_typs cs1 cs2 in 
  List.for_all (fun r -> r != Gt && r != NotCmp) cmps &&
  List.exists (fun r -> r == Less) cmps

let termination_check st v = 
  let last_cs = SMap.find v st.cs_history in 
  constrainsts_smaller st.curr_cs last_cs

let rec implicit_search env aks1 t1 zs node = 
  List.filter_map(fun (v, cand, aks') ->
  let env = Env.add_typs aks' env in
  let ts', zs' = guess_typs (Env.domain_typ env) aks1 in
  let t1'' = subst_typ 
    (List.map (fun ((a, b), c) -> (a, infer_helper c b))
    (List.combine (List.combine (List.map fst aks1) ts') zs)) t1 in
  match cand with 
  | FunT(_, _, _, ImplicitModule) -> 
    let argTs, ExT(ex, resT), aks2 = expand_function cand in
    assert (ex = []);
    let ts2, zs2 = guess_typs (Env.domain_typ env) aks2 in
    let argTs = List.map (subst_typ (subst aks2 ts2)) argTs in
    let resT = (subst_typ (subst aks2 ts2) resT) in
    let sub = try Some (Sub.sub_typ env resT t1'' (varTs aks2)) with Sub.Sub _ -> None in
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
    try Sub.sub_typ env cand t1'' (varTs aks1); 
      Some ((EL.VarE (v@@nowhere_region))@@nowhere_region, cand, Env.add_val v cand env) with Sub.Sub _ -> None) 
      (impl_candidates node)

type error = 
    | None_found
    | Ambiguity (* of ? list*)
    | Termination

let string_of_error e = 
  "implicit resolve failed: " ^
  match e with 
  | None_found -> "none matching"
  | Ambiguity -> "ambiguity"
  | Termination -> "not terminating"

exception ImplSearch of error

type result = Types.var * Syntax.exp * IL.exp * Env.env

type search_global_state = {
    impls : implicit SMap.t;
    vars: (var list) SMap.t;

    unique : varset;
    never : PSet.t;
    to_retry : PSet.t;

    new_info : int SMap.t;
    size : int SMap.t;
    unique_size : int SMap.t;

    errors : error SMap.t;
    results : result SMap.t
}

let update_counter v c1 c2 state = {state with to_retry = if PSet.find_opt (c1, v) state.to_retry == None then state.to_retry else 
                                                              PSet.add (c2, v) (PSet.remove (c1, v) state.to_retry);
                                                new_info = SMap.add v c2 state.new_info}

let update_new_info_var state v id = 
  if SMap.find_opt id state.vars == None then state else
  let st' = List.fold_left (fun st v' -> 
      if v == v' || SMap.find_opt v' st.results != None then st else 
      let c = SMap.find v' st.new_info in
      let st' = update_counter v' c (c + 1) st in
      let sz = SMap.find v' st.size in
      let usz = SMap.find v' st.unique_size in
      let st'' = {st' with size = SMap.add v' (sz - 1) st'.size;
                           never = if PSet.find_opt (sz, v') state.never == None then state.never else 
                                      PSet.add (sz - 1, v') (PSet.remove (sz, v') state.never)} in
      if sz - 1 == usz then 
        {st'' with never = PSet.remove (sz - 1, v') st''.never;
                   to_retry = PSet.remove (c + 1, v') st''.to_retry;
                   unique = VarSet.add v' st''.unique}
      else st''
  ) state (SMap.find id state.vars) in
  {st' with vars = SMap.remove id st'.vars}

let update_new_info v state = 
  let vars = List.map (fun x -> string_of_int x.id) (undet_typ (SMap.find v state.impls).tvar) in 
  List.fold_left (fun st id -> update_new_info_var st v id) state vars

let resolve_implicit env v st = 
  let i = SMap.find v st.impls in 
  match implicit_search env i.aks i.t i.zs i.node with 
  | [] -> Left None_found
  | [(e, t', env')] -> let st' = update_new_info v st in
                       let _, _, f = Sub.sub_typ env t' i.tvar (varTs i.aks) in Right ((i.v, e, f, env'), st')
  | res -> Left Ambiguity

let rec resolve_step env state = 
  if not (VarSet.is_empty state.unique) then 
    resolve_step env (resolve_step_unique env state)
  else if not (PSet.is_empty state.never) then 
    resolve_step env (resolve_step_never env state)
  else if not (PSet.is_empty state.to_retry) && fst (PSet.max_elt state.to_retry) > 0 then
    resolve_step env (resolve_step_new_info env state)
  else if not (PSet.is_empty state.to_retry) then
    let _, v = PSet.min_elt state.to_retry in 
    raise (ImplSearch (SMap.find v state.errors))
  else 
    state
and resolve_step_unique env state = 
  let v = VarSet.min_elt state.unique in 
  match resolve_implicit env v state with
    | Left e -> raise (ImplSearch e)
    | Right (res, st') -> {st' with results = SMap.add v res st'.results;
                                    unique = VarSet.remove v st'.unique}
and resolve_step_never env state = 
  let c, v = PSet.min_elt state.never in
  match resolve_implicit env v state with 
    | Left None_found -> raise (ImplSearch None_found)
    | Left e -> {state with never = PSet.remove (c, v) state.never; 
                            errors = SMap.add v e state.errors;
                            to_retry = PSet.add (0, v) state.to_retry;
                            new_info = SMap.add v 0 state.new_info}
    | Right (res, st') -> {st' with never = PSet.remove (c, v) st'.never;
                                    results = SMap.add v res st'.results}
and resolve_step_new_info env state = 
  let c, v = PSet.max_elt state.to_retry in
  match resolve_implicit env v state with 
    | Left None_found -> raise (ImplSearch None_found)
    | Left e -> update_counter v c 0 {state with errors = SMap.add v e state.errors}
    | Right (res, st') -> {st' with to_retry = PSet.remove (c, v) st'.to_retry;
                                    results = SMap.add v res st'.results}

let init_state impls = 
  let uss = List.fold_left (fun s i -> SMap.add i.v (undet_typ i.tvar) s) SMap.empty impls in
  let vars = List.fold_left (fun vs i ->
    List.fold_left (fun vs' u -> 
      let id = string_of_int u.id in 
      match SMap.find_opt id vs' with
      | None -> SMap.add id [i.v] vs'
      | Some res -> SMap.add id (i.v :: res) vs'
    ) vs (SMap.find i.v uss)
  ) SMap.empty impls in 
  let unique, never = List.partition (fun i -> 
    List.for_all (fun u -> List.length (SMap.find (string_of_int u.id) vars) == 1) (SMap.find i.v uss)
  ) impls in
  let size = List.fold_left (fun vs i ->
    SMap.add i.v (List.length (SMap.find i.v uss)) vs
  ) SMap.empty impls in
  let usize = List.fold_left (fun vs i ->
    SMap.add i.v (List.length (List.filter (fun u -> List.length (SMap.find (string_of_int u.id) vars) == 1) 
      (SMap.find i.v uss))) vs
  ) SMap.empty impls in
    {impls = List.fold_left (fun s i -> SMap.add i.v i s) SMap.empty impls;
     vars = vars;
     unique = List.fold_left (fun s i -> VarSet.add i.v s) VarSet.empty unique;
     never = List.fold_left (fun s i -> PSet.add (SMap.find i.v size, i.v) s) PSet.empty never;
     to_retry = PSet.empty;
     new_info = List.fold_left (fun s i -> SMap.add i.v 0 s) SMap.empty impls;
     size = size;
     unique_size = usize;
     errors = SMap.empty;
     results = SMap.empty}

let resolve_implicits env impls = let res = try resolve_step env (init_state impls)
    with ImplSearch e -> error nowhere_region (string_of_error e) in
  List.map snd (SMap.bindings res.results)

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