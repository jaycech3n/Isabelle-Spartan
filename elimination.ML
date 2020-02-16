(*  Title:      elimination.ML
    Author:     Joshua Chen

Type elimination automation.
*)

structure Elim = struct

(* Elimination rule data *)
structure Rules = Generic_Data (
  type T = thm Termtab.table
  val empty = Termtab.empty
  val extend = I
  val merge = Termtab.merge
    (op aconv o apply2 (Envir.beta_eta_contract o Thm.prop_of))
)

fun register_rule rl =
  let
    val tp = Term.head_of (Lib.type_of_typing (Thm.major_prem_of rl))
    val _ = @{print} tp
  in
    Rules.map (Termtab.update (tp, rl))
  end

fun rules ctxt = map (op #2) (Termtab.dest (Rules.get (Context.Proof ctxt)))

(* Set up [elims] attribute *)
val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>elims\<close>
    (Scan.lift (Scan.succeed (Thm.declaration_attribute register_rule))) ""
  #> Global_Theory.add_thms_dynamic (\<^binding>\<open>elims\<close>,
      fn context => (rules (Context.proof_of context)))
)


end
