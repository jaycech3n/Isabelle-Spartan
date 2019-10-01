structure Util :
sig

val dest_typing: term -> term * term
val dest_Id: term -> term * term * term
val has_subterm: term list -> term -> bool

end = struct

fun dest_typing tm = case tm of
    Const (\<^const_name>\<open>has_type\<close>, _) $ t $ T => (t, T)
  | _ => error "dest_typing"

fun dest_Id tm = case tm of
    Const (\<^const_name>\<open>Id\<close>, _) $ A $ x $ y => (A, x, y)
  | _ => error "dest_Id"

fun has_subterm tms =
  Term.exists_subterm (foldl1 (op orf) (map (fn t => fn s => Term.aconv_untyped (s, t)) tms))


end
