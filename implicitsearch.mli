type implicit

val unresolved_impls : implicit list ref

val create_implicit : Types.var -> Types.typ -> (Types.var * Types.kind) list -> Types.infer ref list -> Types.typ -> implicit

val resolve_implicits : Env.env -> implicit list -> (Types.var * Syntax.exp * IL.exp * Env.env) list

val expand_function : Types.typ -> ((Types.typ) list  * Types.extyp * (Types.var * Types.kind) list)

type implicit_tree

val register_impl_bind : Types.var -> Types.typ -> (Types.var * Types.kind) list -> unit

val remove_last_impl_bind : unit -> unit

val dummy_subst : IL.exp IL.subst -> IL.exp -> IL.exp

val filter_out_implicit_related : (Types.infer ref list) -> (Types.infer ref list)