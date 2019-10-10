structure Implicit_Args =
struct

fun annotations_of tm =
  let
    val idx = Term.maxidx_of_term tm

    (* fun  *)

    fun split_annotation (Const (\<^const_name>\<open>imp_annotation\<close>, _) $ t $ T) = [(t,T)]
      | split_annotation _ = []
  in
    split_annotation (Type.strip_constraints tm)
    @ (case tm of
        t $ u => annotations_of t @ annotations_of u
      | Abs (_, _, t) => annotations_of t
      | _ => [])
  end




end
