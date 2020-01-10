structure Lib :
sig

(*Lists*)
val max: ('a * 'a -> bool) -> 'a list -> 'a
val maxint: int list -> int

(*Terms*)
val is_rigid: term -> bool
val dest_eq: term -> term * term
val mk_Var: string -> int -> typ -> term

val is_typing: term -> bool
val dest_typing: term -> term * term
val term_of_typing: term -> term
val type_of_typing: term -> term
val dest_Id: term -> term * term * term
val mk_Pi: term -> term -> term -> term

(*Subterms*)
val has_subterm: term list -> term -> bool
val fold_aterms: (int -> term -> 'a list -> 'a) -> term -> 'a

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

(* Object *)

fun is_typing (Const (\<^const_name>\<open>has_type\<close>, _) $ _ $ _) = true
  | is_typing _ = false

fun dest_typing (Const (\<^const_name>\<open>has_type\<close>, _) $ t $ T) = (t, T)
  | dest_typing _ = error "dest_typing"

val term_of_typing = #1 o dest_typing
val type_of_typing = #2 o dest_typing

fun dest_Id tm = case tm of
    Const (\<^const_name>\<open>Id\<close>, _) $ A $ x $ y => (A, x, y)
  | _ => error "dest_Id"

fun mk_Pi v typ body = Const (\<^const_name>\<open>Pi\<close>, dummyT) $ typ $ lambda v body


(** Subterms **)

fun has_subterm tms =
  Term.exists_subterm
    (foldl1 (op orf) (map (fn t => fn s => Term.aconv_untyped (s, t)) tms))

(*
  Souped-up version of Term.fold_aterms. At each node n in the AST, the function
  f is additionally passed a unique index i and a list of the results of f at
  all children of n.
*)
fun fold_aterms f t =
  let
    fun map_aux t i =
      let
        val (head, args) = Term.strip_comb t
        val (args', i') = fold_map map_aux args i
        val i'' = maxint [i, i', maxidx_of_term head] + 1
      in
        (f i'' head args', i'')
      end
  in
    #1 (map_aux t 0)
  end


(** Orderings **)

fun subterm_order t1 t2 =
  if has_subterm [t1] t2 then LESS
  else if has_subterm [t2] t1 then GREATER
  else EQUAL

fun cond_order o1 o2 = case o1 of EQUAL => o2 | _ => o1


end
