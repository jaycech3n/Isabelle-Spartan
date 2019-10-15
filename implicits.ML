structure Implicits :
sig

val implicit_defs: Proof.context -> (term * term) Symtab.table
val implicit_defs_attr: attribute
val iargs_of: term -> term list
val raw_iinfo_of: term -> (term * term) list

end = struct

structure Defs = Generic_Data (
  type T = (term * term) Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (Term.aconv o #1)
)

val implicit_defs = Defs.get o Context.Proof

val implicit_defs_attr = Thm.declaration_attribute (fn th =>
  let
    val (t, def) = Lib.dest_eq (Thm.prop_of th)
    val (head, args) = Term.strip_comb t
    val def' = fold_rev lambda args def
  in
    Defs.map (Symtab.update (Term.term_name head, (head, def')))
  end)

fun aux_iargs_of tm =
  let
    fun iarg (t as Const (\<^const_name>\<open>iarg\<close>, _) $ _) = [t]
      | iarg _ = []
  in
    iarg tm
    @ (case tm of
        Const (\<^const_name>\<open>iinfo\<close>, _) $ _ $ _ => []
      | t $ u => aux_iargs_of t @ aux_iargs_of u
      | Abs (_, _, t) => aux_iargs_of t
      | _ => [])
  end

fun iargs_of tm = distinct (op =) (aux_iargs_of tm)

fun raw_iinfo_of tm =
  let
    fun split_annotation (Const (\<^const_name>\<open>iinfo\<close>, _) $ t $ T) = [(t,T)]
      | split_annotation _ = []
  in
    split_annotation tm
    @ (case tm of
        t $ u => raw_iinfo_of t @ raw_iinfo_of u
      | Abs (_, _, t) => raw_iinfo_of t
      | _ => [])
  end



end
