theory Lambda
imports
  Pure
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"

begin

declare [[names_short, eta_contract=false]]


section \<open>Logical framework types\<close>

\<comment>\<open>Meta-terms\<close>
class Mt
default_sort Mt

typedecl ('a, 'b) Pi
typedecl 'a Type

instance Pi   :: (\<open>Mt\<close>, \<open>Mt\<close>) \<open>Mt\<close> ..
instance Type :: (\<open>Mt\<close>) \<open>Mt\<close> ..

section \<open>Types\<close>

subsection \<open>Typing\<close>

consts has_type :: \<open>['a, 'a Type] \<Rightarrow> prop\<close> ("(2_:/ _)")


subsection \<open>Universes\<close>

axiomatization U :: \<open>'a Type\<close>
axiomatization where hierarchy [intro, simp]: "U: U"


subsection \<open>\<Prod>-type\<close>

axiomatization
  Pi :: \<open>['a Type, 'a \<Rightarrow> 'b Type] \<Rightarrow> ('a, 'b) Pi Type\<close> and
  lam  :: \<open>['a Type, 'a \<Rightarrow> 'b] \<Rightarrow> ('a, 'b) Pi\<close> and
  app  :: \<open>[('a, 'b) Pi, 'a] \<Rightarrow> 'b\<close> ("(1_/ `_)" [120, 121] 120)

syntax
  "_Pi"  :: \<open>[idt, 'a Type, 'b Type] \<Rightarrow> ('a, 'b) Pi Type\<close> ("(2\<Prod>_: _./ _)" 30)
  "_lam" :: \<open>[idt, 'a Type, 'b] \<Rightarrow> 'b\<close> ("(2\<lambda>_: _./ _)" 30)
translations
  "\<Prod>x: A. B" \<rightleftharpoons> "(CONST Pi) A (\<lambda>x. B)"
  "\<lambda>x: A. b" \<rightleftharpoons> "(CONST lam) A (\<lambda>x. b)"

abbreviation Fn (infixr "\<rightarrow>" 40) where "A \<rightarrow> B \<equiv> \<Prod>_: A. B"

axiomatization where

  PiF: "\<lbrakk>A: U; \<And>x. x: A \<Longrightarrow> B x: U\<rbrakk> \<Longrightarrow> \<Prod>x: A. B x: U" and

  PiI [intro]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; A: U\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x: \<Prod>x: A. B x" and

  PiE [elim]: "\<lbrakk>f: \<Prod>x: A. B x; a: A\<rbrakk> \<Longrightarrow> f `a: B a" and

  beta: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; a: A\<rbrakk> \<Longrightarrow> (\<lambda>x: A. b x) `a \<equiv> b a" and

  eta: "f: \<Prod>x: A. B x \<Longrightarrow> \<lambda>x: A. f `x \<equiv> f" and

  Pi_cong: "\<lbrakk>
    A: U;
    \<And>x. x: A \<Longrightarrow> B x: U;
    \<And>x. x: A \<Longrightarrow> B' x: U;
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x
    \<rbrakk> \<Longrightarrow> \<Prod>x: A. B x \<equiv> \<Prod>x: A. B' x" and

  lam_cong: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x \<equiv> c x; A: U\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x \<equiv> \<lambda>x: A. c x"


section \<open>Basic automation\<close>

\<comment>\<open>\<open>subst\<close> method\<close>
ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/eqsubst.ML"

method derive uses rules simps = (rule rules | assumption | rule | subst beta)+


section \<open>Functions\<close>

definition funcomp :: \<open>['a Type, ('b, 'c) Pi, ('a, 'b) Pi] \<Rightarrow> ('a, 'c) Pi\<close>
  where "funcomp A g f \<equiv> \<lambda>x: A. g `(f `x)"

syntax
  "_funcomp" :: "[('b, 'c) Pi, 'a Type, ('a, 'b) Pi] \<Rightarrow> ('a, 'c) Pi" ("(2_ \<circ>\<^bsub>_\<^esub>/ _)" [111, 0, 110] 110)
translations
  "g \<circ>\<^bsub>A\<^esub> f" \<rightleftharpoons> "(CONST funcomp) A g f"

lemma funcompI:
  assumes
    "f: A \<rightarrow> B" and
    "g: \<Prod>x: B. C x" and
    "A: U" and
    "B: U" and
    "\<And>x. x : B \<Longrightarrow> C x: U"
  shows
    "g \<circ>\<^bsub>A\<^esub> f: \<Prod>x: A. C (f`x)"
  unfolding funcomp_def by (derive rules: assms PiE)

lemma funcomp_assoc:
  assumes
    "f: A \<rightarrow> B"
    "g: B \<rightarrow> C"
    "h: \<Prod>x: C. D x"
    "A: U"
  shows
    "(h \<circ>\<^bsub>B\<^esub> g) \<circ>\<^bsub>A\<^esub> f \<equiv> h \<circ>\<^bsub>A\<^esub> g \<circ>\<^bsub>A\<^esub> f"
  unfolding funcomp_def by (derive rules: assms lam_cong PiE)

lemma funcomp_comp:
  assumes
    "\<And>x. x: A \<Longrightarrow> b x: B"
    "\<And>x. x: B \<Longrightarrow> c x: C x"
    "A: U"
  shows
    "(\<lambda>x: B. c x) \<circ>\<^bsub>A\<^esub> (\<lambda>x: A. b x) \<equiv> \<lambda>x: A. c (b x)"
  unfolding funcomp_def by (derive rules: assms lam_cong)

definition id where "id A \<equiv> \<lambda>x: A. x"

lemma idI: "A: U \<Longrightarrow> id A: A \<rightarrow> A"
  and id_comp: "x: A \<Longrightarrow> (id A)`x \<equiv> x"
  unfolding id_def by derive

lemma id_left:
  assumes
    "f: A \<rightarrow> B" "A: U" "B: U"
  shows
    "(id B) \<circ>\<^bsub>A\<^esub> f \<equiv> f"
  unfolding id_def
  apply (subst eta[symmetric, of f]; (subst funcomp_comp)?)
  apply (derive rules: assms PiE eta)
  done

lemma id_right:
  assumes
    "f: A \<rightarrow> B" "A: U" "B: U"
  shows
    "f \<circ>\<^bsub>A\<^esub> (id A) \<equiv> f"
  unfolding id_def
  apply (subst eta[symmetric, of f]; (subst funcomp_comp)?)
  apply (derive rules: assms PiE eta)
  done



end
