text \<open>Preliminary functionality for implicits and elaboration.\<close>

theory Elaboration
imports Spartan

begin

section \<open>Implicit argument notation\<close>

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


section \<open>Elaboration\<close>

ML_file \<open>elaboration.ML\<close>

ML \<open>
val _ = Context.>>
  (Syntax_Phases.term_check 1 "" (fn ctxt => map (Elaboration.prep_holes ctxt)))
\<close>


section \<open>Examples\<close>

text \<open>Want to be able to write, for example:\<close>

definition funcomp_i (infixr "\<circ>" 100)
  where [implicit]: "funcomp_i g f \<equiv> funcomp {A} g (f :> {A} \<rightarrow> ?)"

definition Id_i (infix "=" 100)
  where [implicit]: "x = y \<equiv> (x :> {A}) =\<^bsub>{A}\<^esub> (y :> {A})"

schematic_goal
  assumes "f: A \<rightarrow> B" "g: B \<rightarrow> C" "h: C \<rightarrow> D" "A: U i" "B: U i" "C: U i" "D: U i"
  shows "h \<circ> g \<circ> f: A \<rightarrow> D"
  apply (rule funcompI)
oops

term "(f \<circ> g) \<circ> h"
term "f \<circ> g \<circ> h"
term "(x = y) = (x' = y')"
term "(p :> x = y) = q"

text \<open>And also things like:\<close>

definition [implicit]: "pathinv_i p \<equiv> pathinv {A} {x} {y} (p :> {x} =\<^bsub>{A}\<^esub> {y})"

definition [implicit]: "pathcomp_i p q \<equiv>
  pathcomp {A} {x} {y} {z} (p :> {x} =\<^bsub>{A}\<^esub> {y}) (q :> {y} =\<^bsub>{A}\<^esub> {z})"

bundle pathinv_syntax
begin
  notation pathinv_i ("_\<inverse>" [899] 900)
end

bundle no_pathinv_syntax
begin
  no_notation pathinv_i ("_\<inverse>" [899] 900)
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

term "p\<inverse>\<inverse>"
term "p \<bullet> q\<inverse>"

term "p \<bullet> (q \<bullet> r) = p \<bullet> q \<bullet> r"

end
