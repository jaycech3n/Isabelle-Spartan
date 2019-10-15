text \<open>Preliminary functionality for implicits and elaboration.\<close>

theory Elaboration
imports Spartan

begin

section \<open>Implicit notation\<close>

consts
  iarg   :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> 'a\<close>
  idummy :: \<open>'a\<close> ("?")
  iinfo :: \<open>'a \<Rightarrow> 'a Type \<Rightarrow> 'a\<close> (infix ":>" 5)

syntax
  "_iarg" :: \<open>id_position \<Rightarrow> logic\<close> ("{_}")
translations
  "{x}" \<rightleftharpoons> "CONST iarg (\<lambda>x. ?)"


section \<open>Elaboration\<close>

ML_file \<open>implicits.ML\<close>
ML_file \<open>elaboration.ML\<close>

attribute_setup implicit = \<open>Scan.succeed Implicits.implicit_defs_attr\<close>

ML \<open>
fun probe (n: int) ctxt ts =
  let
    val _ = tracing (
      "======== Syntax phase level " ^ @{make_string} n ^ " ========" ^
      "\nTerms\n-----\n" ^
      (space_implode "\n" (map (fn t => "\<^item> " ^  @{make_string} t) ts))
    )
  in
    ts
  end

val _ = Context.>> (
  Syntax_Phases.term_check ~1 "" (probe ~1)
  #> Syntax_Phases.term_check 0 "" (probe 0)
  #> Syntax_Phases.term_check 1 "" (fn ctxt => map (Elaboration.prep ctxt))
  )
\<close>


section \<open>Examples\<close>

text \<open>Want to be able to write, for example:\<close>

definition funcomp_i (infixr "\<circ>" 100)
  where [implicit]: "funcomp_i g f \<equiv> funcomp {A} g (f :> {A} \<rightarrow> ?)"

definition Id_i (infix "=" 100)
  where [implicit]: "x = y \<equiv> (x :> {A}) =\<^bsub>{A}\<^esub> (y :> {A})"

ML_val \<open>
Implicits.implicit_defs @{context}
\<close>

schematic_goal "g \<circ> f : A" oops

(*
  These need to be handled properly too...
  the implicit arg should be different between instances!
*)
term "(f \<circ> g) \<circ> h"
term "f \<circ> g \<circ> h"
term "(x = y) = (x' = y')"
term "(p :> x = y) = q"

abbreviation "pathinv_i p \<equiv> pathinv {A} {x} {y} (p :> {x} =\<^bsub>{A}\<^esub> {y})"

abbreviation (input) "pathcomp_i p q \<equiv>
  pathcomp {A} {x} {y} {z} (p :> {x} =\<^bsub>{A}\<^esub> {y}) (q :> {y} =\<^bsub>{A}\<^esub> {z})"

bundle pathinv_syntax
begin
  notation pathinv_i ("_\<inverse>")
end

bundle no_pathinv_syntax
begin
  no_notation pathinv_i ("_\<inverse>")
end

bundle pathcomp_syntax
begin
  notation pathcomp_i (infixl "\<bullet>" 120)
end

bundle no_pathcomp_syntax
begin
  no_notation pathcomp_i (infixl "\<bullet>" 120)
end

unbundle pathinv_syntax pathcomp_syntax

term "p \<bullet> q"

end
