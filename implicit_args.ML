structure Implicit_Args :
sig

val iargs_of: term -> string list
val raw_annotations_of: term -> (term * term) list
val prepped: term -> term * (term * term) list

end = struct

fun aux_iargs_of tm =
  let
    val tm' = Type.strip_constraints tm

    fun iarg (Const (\<^const_name>\<open>imp_arg\<close>, _) $ Abs (idt, _, _)) = [idt]
      | iarg _ = []
  in
    iarg tm'
    @ (case tm' of
        Const (\<^const_name>\<open>imp_annotation\<close>, _) $ _ $ _ => []
      | t $ u => aux_iargs_of t @ aux_iargs_of u
      | Abs (_, _, t) => aux_iargs_of t
      | _ => [])
  end

fun iargs_of tm = distinct (op =) (aux_iargs_of tm)

fun raw_annotations_of tm =
  let
    val tm' = Type.strip_constraints tm

    fun split_annotation (Const (\<^const_name>\<open>imp_annotation\<close>, _) $ t $ T) = [(t,T)]
      | split_annotation _ = []
  in
    split_annotation tm'
    @ (case tm' of
        t $ u => raw_annotations_of t @ raw_annotations_of u
      | Abs (_, _, t) => raw_annotations_of t
      | _ => [])
  end

fun conv_iargs new_idx tm =
  let
    fun conv (Const (\<^const_name>\<open>imp_arg\<close>, _) $ Abs (name, _, _)) =
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
      Const (\<^const_name>\<open>imp_dummy\<close>, T) => Util.mk_Var "dummy" new_idx T
    | _ => tm)

fun strip_annotations (Const (\<^const_name>\<open>imp_annotation\<close>, _) $ t $ _) = t
  | strip_annotations (t $ u) = strip_annotations t $ strip_annotations u
  | strip_annotations (Abs (x, T, t)) = Abs (x, T, strip_annotations t)
  | strip_annotations t = t

fun prepped tm =
  let
    val new_idx = maxidx_of_term tm + 1
    val prepped_tm = tm |> strip_annotations |> conv_iargs new_idx
    val prepped_annotations = raw_annotations_of tm
      |> map (apsnd (conv_iargs new_idx o conv_idummy new_idx))
  in
    (prepped_tm, prepped_annotations)
  end


end
