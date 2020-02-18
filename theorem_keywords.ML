(*  Title:      theorem_keywords.ML
    Author:     Makarius Wenzel, Joshua Chen

Schematic theorem commands, to enable statements with implicits.

Modified from code originally written by Makarius Wenzel.
*)

local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword

val long_statement =
  Scan.optional
    (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword)
    Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) =>
        (true, binding, includes, elems, concl))

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [],
        [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows))



fun theorem spec descr =
  Outer_Syntax.local_theory_to_proof' spec ("state " ^ descr)
    ((long_statement || short_statement) >>
      (fn (long, binding, includes, elems, concl) =>
        Specification.schematic_theorem_cmd
          long Thm.theoremK NONE (K I) binding includes elems concl))
in

val _ = theorem \<^command_keyword>\<open>theorem*\<close> "schematic theorem"
val _ = theorem \<^command_keyword>\<open>lemma*\<close> "schematic lemma"
val _ = theorem \<^command_keyword>\<open>corollary*\<close> "schematic corollary"
val _ = theorem \<^command_keyword>\<open>proposition*\<close> "schematic proposition"

end
