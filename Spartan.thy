theory Spartan
imports
  Pure
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"
keywords
  "schematic_subgoal" :: prf_script_goal % "proof"

begin

declare [[names_short, eta_contract=false]]

ML_file \<open>schematic_subgoal.ML\<close>

named_theorems forms and intros and elims and reds and congs


section \<open>Logical framework types\<close>

\<comment>\<open>Meta-terms\<close>
class Mt
default_sort Mt

\<comment>\<open>
  We might consider also having a class MT for meta-types, but then we'd need to mess
  around with the sorts of the arguments of the meta-types and the typing judgment
  constant, and it's not clear this would work.
\<close>

typedecl ('a, 'b) Pi
typedecl ('a, 'b) Sig
typedecl 'a Id
typedecl 'a Type
typedecl Nat

instance Pi   :: (\<open>Mt\<close>, \<open>Mt\<close>) \<open>Mt\<close> ..
instance Sig  :: (\<open>Mt\<close>, \<open>Mt\<close>) \<open>Mt\<close> ..
instance Id   :: (\<open>Mt\<close>) \<open>Mt\<close> ..
instance Type :: (\<open>Mt\<close>) \<open>Mt\<close> ..


section \<open>Types & typing\<close>

subsection \<open>Judgment\<close>

consts has_type :: \<open>['a, 'a Type] \<Rightarrow> prop\<close> ("(2_:/ _)")


subsection \<open>Universes\<close>

axiomatization U :: \<open>'a Type\<close>
axiomatization where hierarchy [forms, intros]: "U: U"


subsection \<open>\<Prod>-type\<close>

axiomatization
  Pi :: \<open>['a Type, 'a \<Rightarrow> 'b Type] \<Rightarrow> ('a, 'b) Pi Type\<close> and
  lam  :: \<open>['a Type, 'a \<Rightarrow> 'b] \<Rightarrow> ('a, 'b) Pi\<close> and
  app  :: \<open>[('a, 'b) Pi, 'a] \<Rightarrow> 'b\<close> ("(1_/ `_)" [120, 121] 120)

syntax
  "_Pi"  :: \<open>[pttrn, 'a Type, 'b Type] \<Rightarrow> ('a, 'b) Pi Type\<close> ("(2\<Prod>_: _./ _)" 30)
  "_lam" :: \<open>[pttrn, 'a Type, 'b] \<Rightarrow> 'b\<close> ("(2\<lambda>_: _./ _)" 30)
translations
  "\<Prod>x: A. B" \<rightleftharpoons> "(CONST Pi) A (\<lambda>x. B)"
  "\<lambda>x: A. b" \<rightleftharpoons> "(CONST lam) A (\<lambda>x. b)"

abbreviation Fn (infixr "\<rightarrow>" 40) where "A \<rightarrow> B \<equiv> \<Prod>_: A. B"

axiomatization where
  PiF [forms]: "\<lbrakk>A: U; \<And>x. x: A \<Longrightarrow> B x: U\<rbrakk> \<Longrightarrow> \<Prod>x: A. B x: U" and

  PiI [intros]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; A: U\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x: \<Prod>x: A. B x" and

  PiE [elims]: "\<lbrakk>f: \<Prod>x: A. B x; a: A\<rbrakk> \<Longrightarrow> f `a: B a" and

  beta [reds]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; a: A\<rbrakk> \<Longrightarrow> (\<lambda>x: A. b x) `a \<equiv> b a" and

  eta [reds]: "f: \<Prod>x: A. B x \<Longrightarrow> \<lambda>x: A. f `x \<equiv> f" and

  Pi_cong [congs]: "\<lbrakk>
    A: U;
    \<And>x. x: A \<Longrightarrow> B x: U;
    \<And>x. x: A \<Longrightarrow> B' x: U;
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x
    \<rbrakk> \<Longrightarrow> \<Prod>x: A. B x \<equiv> \<Prod>x: A. B' x" and

  lam_cong [congs]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x \<equiv> c x; A: U\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x \<equiv> \<lambda>x: A. c x"


subsection \<open>\<Sum>-type\<close>

axiomatization
  Sig    :: \<open>['a Type, 'a \<Rightarrow> 'b Type] \<Rightarrow> ('a, 'b) Sig Type\<close> and
  pair   :: \<open>['a, 'b] \<Rightarrow> ('a, 'b) Sig\<close> ("(2<_,/ _>)") and
  SigInd ::
    \<open>['a Type, 'a \<Rightarrow> 'b Type, ('a, 'b) Sig \<Rightarrow> 'c Type, ['a, 'b] \<Rightarrow> 'c, ('a, 'b) Sig] \<Rightarrow> 'c\<close>

syntax
  "_Sum" :: \<open>[idt, 'a Type, 'b Type] \<Rightarrow> ('a, 'b) Sig Type\<close> ("(2\<Sum>_: _./ _)" 20)
translations
  "\<Sum>x: A. B" \<rightleftharpoons> "(CONST Sig) A (\<lambda>x. B)"

abbreviation Cart (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_: A. B"

axiomatization where
  SigF [forms]: "\<lbrakk>A: U; \<And>x. x : A \<Longrightarrow> B x: U\<rbrakk> \<Longrightarrow> \<Sum>x: A. B x: U" and

  SigI [intros]: "\<lbrakk>a: A; b: B a; \<And>x. x : A \<Longrightarrow> B x: U\<rbrakk> \<Longrightarrow> <a, b>: \<Sum>x: A. B x" and

  SigE [elims]: "\<lbrakk>
    p: \<Sum>x: A. B x;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y>;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U;
    A: U;
    \<And>x. x : A \<Longrightarrow> B x: U
    \<rbrakk> \<Longrightarrow> SigInd A B C f p: C p" and

  Sig_comp [reds]: "\<lbrakk>
    a: A;
    b: B a;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y>;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U;
    \<And>x. x : A \<Longrightarrow> B x: U
    \<rbrakk> \<Longrightarrow> SigInd A B C f <a, b> \<equiv> f a b" and

  Sig_cong [congs]: "\<lbrakk>
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x;
    A: U;
    \<And>x. x : A \<Longrightarrow> B x: U;
    \<And>x. x : A \<Longrightarrow> B' x: U
    \<rbrakk> \<Longrightarrow> \<Sum>x: A. B x \<equiv> \<Sum>x: A. B' x"


subsection \<open>Identity\<close>

axiomatization
  Id    :: \<open>['a Type, 'a, 'a] \<Rightarrow> 'a Id Type\<close> and
  refl  :: \<open>'a \<Rightarrow> 'a Id\<close> and
  IdInd :: \<open>['a Type, ['a, 'a, 'a Id] \<Rightarrow> 'c Type, 'a \<Rightarrow> 'c, 'a, 'a, 'a Id] \<Rightarrow> 'c\<close>

syntax
  "_Id" :: \<open>['a, 'a Type, 'a] \<Rightarrow> 'a Id Type\<close> ("(2_ =\<^bsub>_\<^esub>/ _)" [101, 0, 101] 100)
translations
  "a =\<^bsub>A\<^esub> b" \<rightleftharpoons> "(CONST Id) A a b"

axiomatization where
  IdF [forms]: "\<lbrakk>A: U; a: A; b: A\<rbrakk> \<Longrightarrow> a =\<^bsub>A\<^esub> b: U" and

  IdI [intros]: "a: A \<Longrightarrow> refl a: a =\<^bsub>A\<^esub> a" and

  \<comment>\<open>Unusual formulation of the elimination rule to allow induction in structured Isar proofs.\<close>
  IdE [elims]: "\<lbrakk>
    p: a =\<^bsub>A\<^esub> b;
    a: A;
    b: A;
    \<And>x y p. \<lbrakk>p: x =\<^bsub>A\<^esub> y; x: A; y: A\<rbrakk> \<Longrightarrow> C x y p: U;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x)
    \<rbrakk> \<Longrightarrow> IdInd A C f a b p: C a b p" and

  Id_comp [reds]: "\<lbrakk>
    a: A;
    \<And>x y p. \<lbrakk>x: A; y: A; p: x =\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> C x y p: U;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x)
    \<rbrakk> \<Longrightarrow> IdInd A C f a a (refl a) \<equiv> f a"


section \<open>Basic methods\<close>

\<comment>\<open>\<open>subst\<close> method\<close>
ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/eqsubst.ML"

method forms = rule forms
method intros = rule intros
method elims = rule elims
method congs = rule congs

ML \<open>
fun known_raw_tac ctxt = SUBGOAL (fn (_, i) =>
  let
    val ths = map fst (Facts.props (Proof_Context.facts_of ctxt))
  in
    resolve_tac ctxt ths i
  end)
\<close>

method_setup known_raw =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (HEADGOAL (known_raw_tac ctxt)))\<close>

method known uses facts = (rule facts | solves \<open>known_raw\<close>)
method easy uses facts = (known facts: facts | assumption | simp)

method routine uses facts =
  ( elims; ((known facts: facts)+)?
  | intros; ((known facts: facts)+)?
  | forms; ((known facts: facts)+)?
  | known facts: facts )+

method reduce uses facts =
  subst reds; (
    ( elims; ((known facts: facts)+)?
    | known facts: facts )+
  )?

subsection \<open>Work in progress: identity induction method\<close>

schematic_goal IdE2:
  assumes
    "p: a =\<^bsub>A\<^esub> b" "a: A" "b: A"
    "q: b =\<^bsub>A\<^esub> c" "c: A" "A: U"
    "\<And>x y z p q. \<lbrakk>p: x =\<^bsub>A\<^esub> y; q: y =\<^bsub>A\<^esub> z; x: A; y: A; z: A\<rbrakk> \<Longrightarrow> C x y z p q: U"
    "\<And>x z q. \<lbrakk>x: A; z: A; q: x =\<^bsub>A\<^esub> z\<rbrakk> \<Longrightarrow> f x z q: C x x z (refl x) q"
  shows
    "(IdInd A (\<lambda>x y p. \<Prod>z: A. \<Prod>q: y =\<^bsub>A\<^esub> z. C x y z p q) ?f a b p) `c `q :
      C a b c p q"
apply (routine facts: assms; assumption?)
  apply intros+
    apply fact
    apply (forms; easy)
    apply known
done

ML \<open>
fun id_induction_tac fref tm ctxt =
  Subgoal.FOCUS_PREMS (fn {context = goal_ctxt, params, prems, concl, ...} =>
    let
      val IdE = @{thm IdE}
    in
      @{print} params;
      @{print} prems;
      @{print} concl;
      @{print} tm;
      @{print} (Proof_Context.get_fact_single goal_ctxt fref);
      all_tac
    end
  ) ctxt
\<close>

method_setup idind = \<open>
  Scan.lift Parse.thm --
  Scan.option (Scan.lift (Args.$$$ "pred" -- Args.colon) |-- Args.term)
  >> (fn ((fref, _), tm) => fn ctxt =>
    SIMPLE_METHOD (HEADGOAL (id_induction_tac fref tm ctxt)))
\<close>


section \<open>Functions\<close>

subsection \<open>Composition\<close>

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
  unfolding funcomp_def by (routine facts: assms)

lemma funcomp_assoc:
  assumes
    "f: A \<rightarrow> B"
    "g: B \<rightarrow> C"
    "h: \<Prod>x: C. D x"
    "A: U"
  shows
    "(h \<circ>\<^bsub>B\<^esub> g) \<circ>\<^bsub>A\<^esub> f \<equiv> h \<circ>\<^bsub>A\<^esub> g \<circ>\<^bsub>A\<^esub> f"
  unfolding funcomp_def
  by (congs; known?) (reduce; easy?)+

lemma funcomp_comp [reds]:
  assumes
    "\<And>x. x: A \<Longrightarrow> b x: B"
    "\<And>x. x: B \<Longrightarrow> c x: C x"
    "A: U"
  shows
    "(\<lambda>x: B. c x) \<circ>\<^bsub>A\<^esub> (\<lambda>x: A. b x) \<equiv> \<lambda>x: A. c (b x)"
  unfolding funcomp_def
  by (congs; known?) ((reduce facts: assms | routine facts: assms); easy?)+

subsection \<open>Identity function\<close>

definition id where "id A \<equiv> \<lambda>x: A. x"

lemma idI [intros]: "A: U \<Longrightarrow> id A: A \<rightarrow> A"
  and id_comp [reds]: "x: A \<Longrightarrow> (id A) `x \<equiv> x"
  unfolding id_def by (intros; easy?) reduce

lemma id_left [reds]:
  assumes
    "f: A \<rightarrow> B" "A: U" "B: U"
  shows
    "(id B) \<circ>\<^bsub>A\<^esub> f \<equiv> f"
  unfolding id_def
  by (subst eta[symmetric, of f]; easy?) (reduce facts: eta assms)

lemma id_right [reds]:
  assumes
    "f: A \<rightarrow> B" "A: U" "B: U"
  shows
    "f \<circ>\<^bsub>A\<^esub> (id A) \<equiv> f"
  unfolding id_def
  by (subst eta[symmetric, of f]; easy?) (reduce facts: eta assms)


section \<open>Properties of identity\<close>

text \<open>Example derivation of proof term of symmetry of equality.\<close>

schematic_goal Id_symmetric_derivation:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "x: A" "y: A" "A: U"
  shows
    "?prf: y =\<^bsub>A\<^esub> x"
apply (rule IdE[of _ _ x y]; known?)
  apply (forms; (easy facts: assms))
  apply (intros; easy)
done

definition "inv A x y p \<equiv> IdInd A (\<lambda>x y _. (y =\<^bsub>A\<^esub> x)) (\<lambda>x. refl x) x y p"

lemma Id_symmetric [elims, intros]:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "x: A" "y: A" "A: U"
  shows
    "inv A x y p: y =\<^bsub>A\<^esub> x"
  unfolding inv_def by (routine; easy?)+

lemma inv_comp [reds]:
  assumes
    "x: A" "A: U"
  shows
    "inv A x x (refl x) \<equiv> refl x"
  unfolding inv_def by reduce (routine; easy)+

schematic_goal Id_transitive_derivation:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
    "A: U" "x: A" "y: A" "z: A"
  shows
    "?prf: x =\<^bsub>A\<^esub> z"

text \<open>First induct on \<open>p: x = y\<close>.\<close>
apply (rule IdE2[of p A x y]; known?)
  apply (forms; easy?)

  text \<open>
    We could immediately conclude here, but for symmetry of the resulting term we instead
    induct on \<open>q: x = z\<close>.
  \<close>
  schematic_subgoal for x z q
    apply (rule IdE[of q _ x z]; easy?)
      apply (forms; easy)
      apply (intros; easy)
  done
done

definition "pathcomp A x y z p q \<equiv>
  (IdInd A
    (\<lambda>x y _. \<Prod>z: A. y =\<^bsub>A\<^esub> z \<rightarrow> x =\<^bsub>A\<^esub> z)
    (\<lambda>x. \<lambda>z: A. \<lambda>q: x =\<^bsub>A\<^esub> z. IdInd A (\<lambda>x z _. (x =\<^bsub>A\<^esub> z)) (\<lambda>x. refl x) x z q)
    x y p) `z `q"

lemma Id_transitive [elims, intros]:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
    "A: U" "x: A" "y: A" "z: A"
  shows
    "pathcomp A x y z p q: x =\<^bsub>A\<^esub> z"
  unfolding pathcomp_def by (routine; easy?)+


section \<open>Pairs\<close>

definition "fst A B p \<equiv> SigInd A B (\<lambda>_. A) (\<lambda>x y. x) p"
definition "snd A B p \<equiv> SigInd A B (\<lambda>p. B (fst A B p)) (\<lambda>x y. y) p"

lemma fst [elims]: "\<lbrakk>p: \<Sum>x: A. B x; A: U; \<And>x. x: A \<Longrightarrow> B x: U\<rbrakk> \<Longrightarrow> fst A B p: A"
  unfolding fst_def by routine

lemma fst_of_pair [reds]:
  "\<lbrakk>A: U; \<And>x. x: A \<Longrightarrow> B x: U; a: A; b: B a\<rbrakk> \<Longrightarrow> fst A B <a, b> \<equiv> a"
  unfolding fst_def by reduce

lemma snd [elims]:
  assumes "p: \<Sum>x: A. B x" "A: U" "\<And>x. x: A \<Longrightarrow> B x: U"
  shows "snd A B p: B (fst A B p)"
  unfolding snd_def by ((routine facts: assms | reduce); easy?)+

lemma snd_of_pair [reds]:
  assumes "A: U" "\<And>x. x: A \<Longrightarrow> B x: U" "a: A" "b: B a"
  shows "snd A B <a, b> \<equiv> b"
  unfolding snd_def by ((routine facts: assms | reduce); easy?)+


end
