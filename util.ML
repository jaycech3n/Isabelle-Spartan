structure Util :
sig

val mk_Var: string -> int -> typ -> term

val dest_eq: term -> term * term
val dest_typing: term -> term * term
val has_subterm: term list -> term -> bool
val subterm_order: term -> term -> order
val cond_order: order -> order -> order

val dest_Id: term -> term * term * term
val mk_Pi: term -> term -> term -> term

end = struct

fun mk_Var name idx T = Var ((name, idx), T)

fun dest_eq (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ t $ def) = (t, def)
  | dest_eq _ = error "dest_def"

fun dest_typing (Const (\<^const_name>\<open>has_type\<close>, _) $ t $ T) = (t, T)
  | dest_typing _ = error "dest_typing"

fun has_subterm tms =
  Term.exists_subterm (foldl1 (op orf) (map (fn t => fn s => Term.aconv_untyped (s, t)) tms))

fun subterm_order t1 t2 =
  if has_subterm [t1] t2 then LESS
  else if has_subterm [t2] t1 then GREATER
  else EQUAL

fun cond_order o1 o2 = case o1 of EQUAL => o2 | _ => o1

fun dest_Id tm = case tm of
    Const (\<^const_name>\<open>Id\<close>, _) $ A $ x $ y => (A, x, y)
  | _ => error "dest_Id"

fun mk_Pi v typ body = Const (\<^const_name>\<open>Pi\<close>, dummyT) $ typ $ lambda v body


end
