structure Implicits :
sig

val implicit_defs: Proof.context -> (term * term) Symtab.table
val implicit_defs_attr: attribute
val make_holes: Proof.context -> term -> term

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

fun make_holes ctxt =
  let
    fun iarg_to_earg (Const (\<^const_name>\<open>iarg\<close>, T)) = Const (\<^const_name>\<open>earg\<close>, T)
      | iarg_to_earg t = t

    fun earg_to_var i (Const (\<^const_name>\<open>earg\<close>, T)) _ = Var (("*", i), T)
      | earg_to_var _ t args = list_comb (t, args)

    fun expand i head args =
      let
        fun betapplys (head', args') =
          Term.betapplys (map_aterms iarg_to_earg head', args')
      in
        case head of
          Abs (x, T, t) => list_comb (Abs (x, T, expand i t []), args)
        | _ =>
          case Symtab.lookup (implicit_defs ctxt) (Term.term_name head) of
            SOME (t, def) => betapplys
              (Envir.expand_atom (Term.fastype_of head) (Term.fastype_of t, def),
              args)
          | NONE => list_comb (head, args)
      end
  in
    Lib.fold_aterms expand 0 #> Lib.fold_aterms earg_to_var 0
  end


end
