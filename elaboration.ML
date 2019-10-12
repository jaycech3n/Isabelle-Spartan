structure Elaboration :
sig

val implicit_defs: Proof.context -> term Termtab.table
val implicit_defs_attr: attribute

val iargs_of: term -> term list
val raw_iinfo_of: term -> (term * term) list
val prepped: term -> term * (term * term) list

end = struct

(** Definitions with implicit arguments **)

structure Implicit_Defs = Generic_Data (
  type T = term Termtab.table
  val empty = Termtab.empty
  val extend = I
  val merge = Termtab.merge Term.aconv
)

val implicit_defs = Implicit_Defs.get o Context.Proof

val implicit_defs_attr = Thm.declaration_attribute (fn th =>
  let val (t, def) = Util.dest_eq (Thm.prop_of th)
  in Implicit_Defs.map (Termtab.update (t, def))
  end)


(** Prep phase **)

(*** Expand definitions with implicits ***)




fun aux_iargs_of tm =
  let
    val tm' = Type.strip_constraints tm

    fun iarg (t as Const (\<^const_name>\<open>iarg\<close>, _) $ _) = [t]
      | iarg _ = []
  in
    iarg tm'
    @ (case tm' of
        Const (\<^const_name>\<open>iinfo\<close>, _) $ _ $ _ => []
      | t $ u => aux_iargs_of t @ aux_iargs_of u
      | Abs (_, _, t) => aux_iargs_of t
      | _ => [])
  end

fun iargs_of tm = distinct (op =) (aux_iargs_of tm)

fun raw_iinfo_of tm =
  let
    val tm' = Type.strip_constraints tm

    fun split_annotation (Const (\<^const_name>\<open>iinfo\<close>, _) $ t $ T) = [(t,T)]
      | split_annotation _ = []
  in
    split_annotation tm'
    @ (case tm' of
        t $ u => raw_iinfo_of t @ raw_iinfo_of u
      | Abs (_, _, t) => raw_iinfo_of t
      | _ => [])
  end

fun conv_iargs new_idx tm =
  let
    fun conv (Const (\<^const_name>\<open>iarg\<close>, _) $ Abs (name, _, _)) =
          Util.mk_Var name new_idx dummyT
      | conv (t $ u) = conv t $ conv u
      | conv (Abs (x, T, t)) = Abs (x, T, conv t)
      | conv t = t
  in
    conv (Type.strip_constraints tm)
  end

fun conv_idummy new_idx =
  map_aterms (fn tm =>
    case tm of
      Const (\<^const_name>\<open>idummy\<close>, T) => Util.mk_Var "dummy" new_idx T
    | _ => tm)

fun strip_iinfo (Const (\<^const_name>\<open>iinfo\<close>, _) $ t $ _) = t
  | strip_iinfo (t $ u) = strip_iinfo t $ strip_iinfo u
  | strip_iinfo (Abs (x, T, t)) = Abs (x, T, strip_iinfo t)
  | strip_iinfo t = t

fun prepped tm =
  let
    val new_idx = maxidx_of_term tm + 1
    val prepped_tm = tm |> strip_iinfo |> conv_iargs new_idx
    val prepped_iinfo = raw_iinfo_of tm
      |> map (apsnd (conv_iargs new_idx o conv_idummy new_idx))
  in
    (prepped_tm, prepped_iinfo)
  end


end
