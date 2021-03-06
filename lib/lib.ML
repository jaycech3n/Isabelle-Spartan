structure Lib :
sig

(*Lists*)
val max: ('a * 'a -> bool) -> 'a list -> 'a
val maxint: int list -> int

(*Terms*)
val is_rigid: term -> bool
val dest_eq: term -> term * term
val mk_Var: string -> int -> typ -> term
val lambda_var: term -> term -> term

val is_typing: term -> bool
val dest_typing: term -> term * term
val term_of_typing: term -> term
val type_of_typing: term -> term
val mk_Pi: term -> term -> term -> term

val typing_of_term: term -> term

(*Goals*)
val rigid_typing_concl: term -> bool

(*Subterms*)
val has_subterm: term list -> term -> bool
val subterm_count: term -> term -> int
val subterm_count_distinct: term list -> term -> int
val traverse_term: (term -> term list -> term) -> term -> term
val collect_subterms: (term -> bool) -> term -> term list

(*Orderings*)
val subterm_order: term -> term -> order
val cond_order: order -> order -> order

end = struct


(** Lists **)

fun max gt (x::xs) = fold (fn a => fn b => if gt (a, b) then a else b) xs x
  | max _ [] = error "max of empty list"

val maxint = max (op >)


(** Terms **)

(* Meta *)

val is_rigid = not o is_Var o head_of

fun dest_eq (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ t $ def) = (t, def)
  | dest_eq _ = error "dest_eq"

fun mk_Var name idx T = Var ((name, idx), T)

fun lambda_var x tm =
  let
    fun var_args (Var (idx, T)) = Var (idx, \<^typ>\<open>o\<close> --> T) $ x
      | var_args t = t
  in
    tm |> map_aterms var_args
       |> lambda x
  end

(* Object *)

fun is_typing (Const (\<^const_name>\<open>has_type\<close>, _) $ _ $ _) = true
  | is_typing _ = false

fun dest_typing (Const (\<^const_name>\<open>has_type\<close>, _) $ t $ T) = (t, T)
  | dest_typing _ = error "dest_typing"

val term_of_typing = #1 o dest_typing
val type_of_typing = #2 o dest_typing

fun mk_Pi v typ body = Const (\<^const_name>\<open>Pi\<close>, dummyT) $ typ $ lambda v body

fun typing_of_term tm = \<^const>\<open>has_type\<close> $ tm $ Var (("*?", 0), \<^typ>\<open>o\<close>)


(** Goals **)

fun rigid_typing_concl goal =
  let val concl = Logic.strip_assums_concl goal
  in is_typing concl andalso is_rigid (term_of_typing concl) end


(** Subterms **)

fun has_subterm tms =
  Term.exists_subterm
    (foldl1 (op orf) (map (fn t => fn s => Term.aconv_untyped (s, t)) tms))

fun subterm_count s t =
  let
    fun count (t1 $ t2) i = i + count t1 0 + count t2 0
      | count (Abs (_, _, t)) i = i + count t 0
      | count t i = if Term.aconv_untyped (s, t) then i + 1 else i
  in
    count t 0
  end

(*Number of distinct subterms in `tms` that appear in `tm`*)
fun subterm_count_distinct tms tm =
  length (filter I (map (fn t => has_subterm [t] tm) tms))

(*
  "Folds" a function f over the term structure of t by traversing t from child
  nodes upwards through parents. At each node n in the term syntax tree, f is
  additionally passed a list of the results of f at all children of n.
*)
fun traverse_term f t =
  let
    fun map_aux (Abs (x, T, t)) = Abs (x, T, map_aux t)
      | map_aux t =
          let
            val (head, args) = Term.strip_comb t
            val args' = map map_aux args
          in
            f head args'
          end
  in
    map_aux t
  end

fun collect_subterms f (t $ u) = collect_subterms f t @ collect_subterms f u
  | collect_subterms f (Abs (_, _, t)) = collect_subterms f t
  | collect_subterms f t = if f t then [t] else []


(** Orderings **)

fun subterm_order t1 t2 =
  if has_subterm [t1] t2 then LESS
  else if has_subterm [t2] t1 then GREATER
  else EQUAL

fun cond_order o1 o2 = case o1 of EQUAL => o2 | _ => o1


end
