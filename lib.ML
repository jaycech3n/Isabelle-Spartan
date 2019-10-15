structure Lib :
sig

(*Lists*)
val max: ('a * 'a -> bool) -> 'a list -> 'a
val maxint: int list -> int

(*Term constructors and destructors*)
val mk_Var: string -> int -> typ -> term
val mk_Pi: term -> term -> term -> term
val dest_Id: term -> term * term * term
val dest_eq: term -> term * term
val dest_typing: term -> term * term

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
  Souped-up version of Term.fold_aterms. The mapped function f is additionally passed an
  index i and a list of the results of f at all children of the current node n in the AST.
  i is guaranteed to be distinct for each node n in the AST.
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
