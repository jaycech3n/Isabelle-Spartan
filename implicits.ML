structure Implicits :
sig

val implicit_defs: Proof.context -> (term * term) Symtab.table
val implicit_defs_attr: attribute

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


end
