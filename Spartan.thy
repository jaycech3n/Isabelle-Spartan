chapter \<open>Spartan type theory\<close>

theory Spartan
imports
  Pure
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"
keywords
  "print_coercions" :: thy_decl and
  "schematic_subgoal" :: prf_script_goal % "proof"

begin

declare [[names_short, eta_contract=false]]

ML_file \<open>schematic_subgoal.ML\<close>
ML_file \<open>$ISABELLE_HOME/src/Tools/subtyping.ML\<close>
declare [[coercion_enabled]]

named_theorems forms and intros and elims and reds and congs


section \<open>Types and typing\<close>

subsection \<open>Metatype setup\<close>

class tt
default_sort tt
typedecl o


subsection \<open>Judgments\<close>

axiomatization has_type :: \<open>o \<Rightarrow> o \<Rightarrow> prop\<close> ("(2_:/ _)")


subsection \<open>Universes\<close>

typedecl lvl \<comment>\<open>Universe levels\<close>

axiomatization
  O  :: \<open>lvl\<close> and
  S  :: \<open>lvl \<Rightarrow> lvl\<close> and
  lt :: \<open>lvl \<Rightarrow> lvl \<Rightarrow> prop\<close> (infix "<" 900)
  where
  O_min: "O < S i" and
  lt_S: "i < S i" and
  lt_trans: "i < j \<Longrightarrow> j < k \<Longrightarrow> i < k"

axiomatization U :: \<open>lvl \<Rightarrow> o\<close> where
  U_hierarchy: "i < j \<Longrightarrow> U i: U j" and
  U_cumulative: "A: U i \<Longrightarrow> i < j \<Longrightarrow> A: U j"


subsection \<open>\<Prod>-type\<close>

axiomatization
  Pi  :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o\<close> and
  lam :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o\<close> and
  app :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> ("(1_ `_)" [120, 121] 120)

syntax
  "_Pi"  :: \<open>idt \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<Prod>_: _./ _)" 30)
  "_lam" :: \<open>idt \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<lambda>_: _./ _)" 30)
translations
  "\<Prod>x: A. B" \<rightleftharpoons> "CONST Pi A (\<lambda>x. B)"
  "\<lambda>x: A. b" \<rightleftharpoons> "CONST lam A (\<lambda>x. b)"

abbreviation Fn (infixr "\<rightarrow>" 40) where "A \<rightarrow> B \<equiv> \<Prod>_: A. B"

axiomatization where
  PiF [forms]: "\<lbrakk>A: U i; \<And>x. x: A \<Longrightarrow> B x: U i\<rbrakk> \<Longrightarrow> \<Prod>x: A. B x: U i" and

  PiI [intros]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; A: U i\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x: \<Prod>x: A. B x" and

  PiE [elims]: "\<lbrakk>f: \<Prod>x: A. B x; a: A\<rbrakk> \<Longrightarrow> f `a: B a" and

  beta [reds]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; a: A\<rbrakk> \<Longrightarrow> (\<lambda>x: A. b x) `a \<equiv> b a" and

  eta [reds]: "f: \<Prod>x: A. B x \<Longrightarrow> \<lambda>x: A. f `x \<equiv> f" and

  Pi_cong [congs]: "\<lbrakk>
    A: U i;
    \<And>x. x: A \<Longrightarrow> B x: U i;
    \<And>x. x: A \<Longrightarrow> B' x: U i;
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x
    \<rbrakk> \<Longrightarrow> \<Prod>x: A. B x \<equiv> \<Prod>x: A. B' x" and

  lam_cong [congs]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x \<equiv> c x; A: U i\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x \<equiv> \<lambda>x: A. c x"


subsection \<open>\<Sum>-type\<close>

axiomatization
  Sig    :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o\<close> and
  pair   :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> ("(2<_,/ _>)") and
  SigInd :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o\<close>

syntax
  "_Sum" :: \<open>idt \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<Sum>_: _./ _)" 20)
translations
  "\<Sum>x: A. B" \<rightleftharpoons> "CONST Sig A (\<lambda>x. B)"

abbreviation Cart (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_: A. B"

axiomatization where
  SigF [forms]: "\<lbrakk>A: U i; \<And>x. x: A \<Longrightarrow> B x: U i\<rbrakk> \<Longrightarrow> \<Sum>x: A. B x: U i" and

  SigI [intros]: "\<lbrakk>a: A; b: B a; \<And>x. x : A \<Longrightarrow> B x: U i\<rbrakk> \<Longrightarrow> <a, b>: \<Sum>x: A. B x" and

  SigE [elims]: "\<lbrakk>
    p: \<Sum>x: A. B x;
    A: U i;
    \<And>x. x : A \<Longrightarrow> B x: U i;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U i;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y>
    \<rbrakk> \<Longrightarrow> SigInd A B C f p: C p" and

  Sig_comp [reds]: "\<lbrakk>
    a: A;
    b: B a;
    \<And>x. x: A \<Longrightarrow> B x: U i;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U i;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y>
    \<rbrakk> \<Longrightarrow> SigInd A B C f <a, b> \<equiv> f a b" and

  Sig_cong [congs]: "\<lbrakk>
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x;
    A: U i;
    \<And>x. x : A \<Longrightarrow> B x: U i;
    \<And>x. x : A \<Longrightarrow> B' x: U i
    \<rbrakk> \<Longrightarrow> \<Sum>x: A. B x \<equiv> \<Sum>x: A. B' x"


subsection \<open>Identity type\<close>

axiomatization
  Id    :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> and
  refl  :: \<open>o \<Rightarrow> o\<close> and
  IdInd :: \<open>o \<Rightarrow> (o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close>

syntax
  "_Id" :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2_ =\<^bsub>_\<^esub>/ _)" [101, 0, 101] 100)
translations
  "a =\<^bsub>A\<^esub> b" \<rightleftharpoons> "CONST Id A a b"

axiomatization where
  IdF [forms]: "\<lbrakk>A: U i; a: A; b: A\<rbrakk> \<Longrightarrow> a =\<^bsub>A\<^esub> b: U i" and

  IdI [intros]: "a: A \<Longrightarrow> refl a: a =\<^bsub>A\<^esub> a" and

  IdE [elims]: "\<lbrakk>
    p: a =\<^bsub>A\<^esub> b;
    a: A;
    b: A;
    \<And>x y p. \<lbrakk>p: x =\<^bsub>A\<^esub> y; x: A; y: A\<rbrakk> \<Longrightarrow> C x y p: U i;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x)
    \<rbrakk> \<Longrightarrow> IdInd A C f a b p: C a b p" and

  Id_comp [reds]: "\<lbrakk>
    a: A;
    \<And>x y p. \<lbrakk>x: A; y: A; p: x =\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> C x y p: U i;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x)
    \<rbrakk> \<Longrightarrow> IdInd A C f a a (refl a) \<equiv> f a"


section \<open>Basic methods\<close>

ML_file \<open>lib.ML\<close>

\<comment>\<open>\<open>subst\<close> method\<close>
ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/eqsubst.ML"

ML \<open>
(* An assumption tactic that doesn't instantiate schematic variables *)
val assm'_tac = Subgoal.FOCUS (fn {context, prems, ...} =>
  HEADGOAL (resolve_tac context prems))

fun known_raw_tac ctxt = SUBGOAL (fn (_, i) =>
  let
    val ths = map fst (Facts.props (Proof_Context.facts_of ctxt))
  in
    resolve_tac ctxt ths i ORELSE assm'_tac ctxt i
  end)
\<close>

method_setup known_raw =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (HEADGOAL (known_raw_tac ctxt)))\<close>

method known uses facts = (rule facts | known_raw)

method easy uses facts = (known facts: facts | assumption)

method forms = rule forms

method intros = rule intros
  \<comment>\<open>Introduce a canonical constructor\<close>

method elims = (rule elims, (known | assumption)); (known | assumption+)?
  \<comment>\<open>Prove a statement subject to immediate discharge of the first condition\<close>

method congs = rule congs

method routine uses facts =
  ( (forms | intros | elims); ((known facts: facts)+)?
  | known facts: facts )+

method reduce uses facts = subst reds; ((known facts: facts)+)?


subsection \<open>Identity induction\<close>

ML_file \<open>equality.ML\<close>

method_setup equality = \<open>Scan.lift Parse.thm >> (fn (fact, _) => fn ctxt =>
  CONTEXT_METHOD (K (Equality.equality_context_tac fact ctxt)))\<close>


section \<open>Functions\<close>

\<comment>\<open>Coerce object lambdas to meta-lambdas when needed.\<close>
abbreviation (input) lam_to_lambda :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close>
  where "lam_to_lambda f \<equiv> \<lambda>x. f `x"

declare [[coercion lam_to_lambda]]


subsection \<open>Composition\<close>

definition "funcomp A g f \<equiv> \<lambda>x: A. g `(f `x)"

syntax
  "_funcomp" :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2_ \<circ>\<^bsub>_\<^esub>/ _)" [111, 0, 110] 110)
translations
  "g \<circ>\<^bsub>A\<^esub> f" \<rightleftharpoons> "CONST funcomp A g f"

lemma funcompI:
  assumes
    "f: A \<rightarrow> B" and
    "g: \<Prod>x: B. C x" and
    "A: U i" and
    "B: U i" and
    "\<And>x. x : B \<Longrightarrow> C x: U i"
  shows
    "g \<circ>\<^bsub>A\<^esub> f: \<Prod>x: A. C (f `x)"
  unfolding funcomp_def by routine

lemma funcomp_assoc:
  assumes
    "f: A \<rightarrow> B"
    "g: B \<rightarrow> C"
    "h: \<Prod>x: C. D x"
    "A: U i"
  shows
    "(h \<circ>\<^bsub>B\<^esub> g) \<circ>\<^bsub>A\<^esub> f \<equiv> h \<circ>\<^bsub>A\<^esub> g \<circ>\<^bsub>A\<^esub> f"
  unfolding funcomp_def
  by (congs; known?) (reduce | routine)+

lemma funcomp_comp [reds]:
  assumes
    "\<And>x. x: A \<Longrightarrow> b x: B"
    "\<And>x. x: B \<Longrightarrow> c x: C x"
    "A: U i"
  shows
    "(\<lambda>x: B. c x) \<circ>\<^bsub>A\<^esub> (\<lambda>x: A. b x) \<equiv> \<lambda>x: A. c (b x)"
  unfolding funcomp_def
  by (congs; known?) reduce+

subsection \<open>Identity function\<close>

definition id where "id A \<equiv> \<lambda>x: A. x"

lemma
  idI: "A: U i \<Longrightarrow> id A: A \<rightarrow> A" and
  id_comp [reds]: "x: A \<Longrightarrow> (id A) `x \<equiv> x"
  unfolding id_def
  by (intros; easy) reduce

lemma id_left [reds]:
  assumes
    "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows
    "(id B) \<circ>\<^bsub>A\<^esub> f \<equiv> f"
  unfolding id_def
  by (subst eta[symmetric, of f]; known?) (reduce; (routine facts: eta)?)

lemma id_right [reds]:
  assumes
    "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows
    "f \<circ>\<^bsub>A\<^esub> (id A) \<equiv> f"
  unfolding id_def
  by (subst eta[symmetric, of f]; known?) (reduce; (routine facts: eta)?)


section \<open>Identity\<close>

schematic_goal Id_symmetric_derivation:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "x: A" "y: A" "A: U i"
  shows
    "?prf: y =\<^bsub>A\<^esub> x"
  by (equality \<open>p: _\<close>)

(* TODO: automatically generate definitions for the terms derived in the above manner. *)

definition "pathinv A x y p \<equiv> IdInd A (\<lambda>x y _. y =\<^bsub>A\<^esub> x) (\<lambda>x. refl x) x y p"

lemma Id_symmetric:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "x: A" "y: A" "A: U i"
  shows
    "pathinv A x y p: y =\<^bsub>A\<^esub> x"
  unfolding pathinv_def by (rule Id_symmetric_derivation assms)+

lemma pathinv_comp [reds]:
  assumes
    "x: A" "A: U i"
  shows
    "pathinv A x x (refl x) \<equiv> refl x"
  unfolding pathinv_def by reduce routine

schematic_goal Id_transitive_derivation:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
    "A: U i" "x: A" "y: A" "z: A"
  shows
    "?prf: x =\<^bsub>A\<^esub> z"
apply (equality \<open>p: _\<close>)
  schematic_subgoal premises for x q
    apply (equality \<open>q: _\<close>)
  done
done

definition "pathcomp A x y z p q \<equiv>
  (IdInd A
    (\<lambda>x y _. y =\<^bsub>A\<^esub> z \<rightarrow> x =\<^bsub>A\<^esub> z)
    (\<lambda>x. \<lambda>q: x =\<^bsub>A\<^esub> z. IdInd A (\<lambda>x z _. (x =\<^bsub>A\<^esub> z)) (\<lambda>x. refl x) x z q)
    x y p) `q"

lemma Id_transitive:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
    "A: U i" "x: A" "y: A" "z: A"
  shows
    "pathcomp A x y z p q: x =\<^bsub>A\<^esub> z"
  unfolding pathcomp_def by (rule Id_transitive_derivation assms)+

lemma pathcomp_comp [reds]:
  "\<lbrakk>A: U i; a: A\<rbrakk> \<Longrightarrow> pathcomp A a a a (refl a) (refl a) \<equiv> refl a"
  unfolding pathcomp_def by (reduce | routine | easy)+


section \<open>Pairs\<close>

definition "fst A B p \<equiv> SigInd A B (\<lambda>_. A) (\<lambda>x y. x) p"
definition "snd A B p \<equiv> SigInd A B (\<lambda>p. B (fst A B p)) (\<lambda>x y. y) p"

lemma fst [elims]: "\<lbrakk>p: \<Sum>x: A. B x; A: U i; \<And>x. x: A \<Longrightarrow> B x: U i\<rbrakk> \<Longrightarrow> fst A B p: A"
  unfolding fst_def by routine

lemma fst_of_pair [reds]:
  "\<lbrakk>A: U i; \<And>x. x: A \<Longrightarrow> B x: U i; a: A; b: B a\<rbrakk> \<Longrightarrow> fst A B <a, b> \<equiv> a"
  unfolding fst_def by reduce

lemma snd [elims]:
  assumes "p: \<Sum>x: A. B x" "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "snd A B p: B (fst A B p)"
  unfolding snd_def by (reduce | routine)+

lemma snd_of_pair [reds]:
  assumes "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i" "a: A" "b: B a"
  shows "snd A B <a, b> \<equiv> b"
  unfolding snd_def by (reduce | routine)+


end
