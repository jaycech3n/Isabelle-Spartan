theory Implicits
imports Spartan

begin

text \<open>This theory provides functionality for implicits and elaboration.\<close>

section \<open>Implicit arguments\<close>

consts
  iarg   :: \<open>(o \<Rightarrow> o) \<Rightarrow> o\<close>
  idummy :: \<open>o\<close> ("?")
  iannot :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> (infix ":>" 5)

syntax
  "_iarg" :: \<open>id_position \<Rightarrow> logic\<close> ("{_}")
translations
  "{x}" \<rightleftharpoons> "CONST iarg (\<lambda>x. ?)"

ML_file \<open>implicits.ML\<close>

attribute_setup implicit = \<open>Scan.succeed Implicits.implicit_defs_attr\<close>

(*This is old preparatory work for term elaboration and should be cleaned up in
  the near future*)
ML_file \<open>elaboration.ML\<close>

ML \<open>
val _ = Context.>>
  (Syntax_Phases.term_check 1 "" (fn ctxt => map (Elaboration.prep_holes ctxt)))
\<close>


section \<open>Notation\<close>

definition Id_i (infix "=" 110)
  where [implicit]: "Id_i x y \<equiv> x =\<^bsub>{A}\<^esub> y"

definition funcomp_i (infixr "\<circ>" 110)
  where [implicit]: "funcomp_i g f \<equiv> g \<circ>\<^bsub>{A}\<^esub> f"

definition pathinv_i ("_\<inverse>" [1000])
  where [implicit]: "pathinv_i p \<equiv> pathinv {A} {x} {y} p"

definition pathcomp_i (infixl "\<bullet>" 120)
  where [implicit]: "pathcomp_i p q \<equiv> pathcomp {A} {x} {y} {z} p q"

translations
  "x = y" \<leftharpoondown> "x =\<^bsub>A\<^esub> y"
  "g \<circ> f" \<leftharpoondown> "g \<circ>\<^bsub>A\<^esub> f"
  "(p)\<inverse>" \<leftharpoondown> "CONST pathinv A x y p"
  "(p \<bullet> q)" \<leftharpoondown> "CONST pathcomp A x y z p q"


end
