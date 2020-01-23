theory Implicits
imports Spartan

begin


section \<open>Implicit arguments\<close>

text \<open>
  \<open>?\<close> is used to mark implicit arguments in definitions, while \<open>!\<close> is expanded
  immediately for elaboration in statements. 
\<close>

consts
  iarg :: \<open>'a\<close> ("?")
  earg :: \<open>'a\<close> ("!")

ML_file \<open>implicits.ML\<close>

attribute_setup implicit = \<open>Scan.succeed Implicits.implicit_defs_attr\<close>

ML \<open>
val _ = Context.>>
  (Syntax_Phases.term_check 1 "" (fn ctxt => map (Implicits.make_holes ctxt)))
\<close>


section \<open>Notation\<close>

definition Id_i (infix "=" 110)
  where [implicit]: "Id_i x y \<equiv> x =\<^bsub>?\<^esub> y"

definition funcomp_i (infixr "\<circ>" 120)
  where [implicit]: "funcomp_i g f \<equiv> g \<circ>\<^bsub>?\<^esub> f"

definition pathinv_i ("_\<inverse>" [1000])
  where [implicit]: "pathinv_i p \<equiv> pathinv ? ? ? p"

definition pathcomp_i (infixl "\<bullet>" 120)
  where [implicit]: "pathcomp_i p q \<equiv> pathcomp ? ? ? ? p q"

definition fst_i ("_.1" [1000])
  where [implicit]: "p.1 \<equiv> fst ? ? p"

definition snd_i ("_.2" [1000])
  where [implicit]: "p.2 \<equiv> snd ? ? p" 

(* translations
  "x = y" \<leftharpoondown> "x =\<^bsub>A\<^esub> y"
  "g \<circ> f" \<leftharpoondown> "g \<circ>\<^bsub>A\<^esub> f"
  "p\<inverse>" \<leftharpoondown> "CONST pathinv A x y p"
  "p \<bullet> q" \<leftharpoondown> "CONST pathcomp A x y z p q"
  "p.1" \<leftharpoondown> "CONST fst A B p"
  "p.2" \<leftharpoondown> "CONST snd A B p" *)


end
