structure Lib :
sig

(*Lists*)
val max: ('a * 'a -> bool) -> 'a list -> 'a

(*Term constructors and destructors*)
val mk_Var: string -> int -> typ -> term
val mk_Pi: term -> term -> term -> term
val dest_Id: term -> term * term * term
val dest_eq: term -> term * term
val dest_typing: term -> term * term

(*Subterms*)
val has_subterm: term list -> term -> bool
val map_aterms_distinct_index: (int -> term -> term) -> term -> term

(*Orderings*)
val subterm_order: term -> term -> order
val cond_order: order -> order -> order

end = struct

(** Lists **)
fun max gt (x::xs) = fold (fn a => fn b => if gt (a, b) then a else b) xs x
  | max _ [] = error "max of empty list"


(** Constructors and destructors **)

fun mk_Var name idx T = Var ((name, idx), T)

fun mk_Pi v typ body = Const (\<^const_name>\<open>Pi\<close>, dummyT) $ typ $ lambda v body

fun dest_Id tm = case tm of
    Const (\<^const_name>\<open>Id\<close>, _) $ A $ x $ y => (A, x, y)
  | _ => error "dest_Id"

fun dest_eq (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ t $ def) = (t, def)
  | dest_eq _ = error "dest_def"

fun dest_typing (Const (\<^const_name>\<open>has_type\<close>, _) $ t $ T) = (t, T)
  | dest_typing _ = error "dest_typing"


(** Subterms **)

fun has_subterm tms =
  Term.exists_subterm (foldl1 (op orf) (map (fn t => fn s => Term.aconv_untyped (s, t)) tms))

(*
  Extends Term.map_aterms by passing f an extra index value that is guaranteed to be
  distinct for distinct nodes in the AST.
*)
fun map_aterms_distinct_index f t =
  let
    fun map_aux n t =
      let
        val (head, args) = Term.strip_comb t
        val args' = map_index (fn (i, t) => map_aux (n + 1 + i) t) args
        val idx =
          if null args' then n
          else max (op >) (map Term.maxidx_of_term (head :: args')) + 1
      in
        Term.list_comb (f idx head, args')
      end
  in
    map_aux 0 t
  end


(** Orderings **)

fun subterm_order t1 t2 =
  if has_subterm [t1] t2 then LESS
  else if has_subterm [t2] t1 then GREATER
  else EQUAL

fun cond_order o1 o2 = case o1 of EQUAL => o2 | _ => o1


end
