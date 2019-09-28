theory Spartan
imports
  Pure
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"

begin

declare [[names_short, eta_contract=false]]

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
  "_Pi"  :: \<open>[idt, 'a Type, 'b Type] \<Rightarrow> ('a, 'b) Pi Type\<close> ("(2\<Prod>_: _./ _)" 30)
  "_lam" :: \<open>[idt, 'a Type, 'b] \<Rightarrow> 'b\<close> ("(2\<lambda>_: _./ _)" 30)
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
    PROP P a b p;
    \<And>x y p. \<lbrakk>p: x =\<^bsub>A\<^esub> y; x: A; y: A; PROP P x y p\<rbrakk> \<Longrightarrow> C x y p: U;
    \<And>x. \<lbrakk>x: A; PROP P x x (refl x)\<rbrakk> \<Longrightarrow> f x: C x x (refl x)
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

method easy uses facts = (rule facts | fact | assumption | simp)

method routine uses facts =
  ( elims; ((easy facts: facts)+)?
  | intros; ((easy facts: facts)+)?
  | forms; ((easy facts: facts)+)?
  | easy facts: facts )+

method reduce uses facts =
  subst reds; (
    ( elims; ((easy facts: facts)+)?
    | easy facts: facts )+
  )?

subsection \<open>Work in progress: identity induction method\<close>

lemma swap_imp:
  "(PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP R) \<equiv> (PROP Q \<Longrightarrow> PROP P \<Longrightarrow> PROP R)"
proof
  assume 1: "PROP Q" and 2: "PROP P"
  { assume *: "PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP R"
    show "PROP R" by (fact *[OF 2 1]) }
  { assume *: "PROP Q \<Longrightarrow> PROP P \<Longrightarrow> PROP R"
    show "PROP R" by (fact *[OF 1 2]) }
qed

definition IMP (infixr "IMP" 1)
  where "(P IMP Q) \<equiv> (PROP P \<Longrightarrow> PROP Q)"

lemma elim_imp_to_IMP:
  "PROP P \<Longrightarrow> (PROP P IMP PROP Q) \<Longrightarrow> PROP Q"
  by (simp add: IMP_def)

lemma simp_IMP_to_imp:
  "(PROP P IMP PROP Q IMP PROP R) \<equiv> (PROP Q \<Longrightarrow> PROP P IMP PROP R)"
unfolding IMP_def proof
  assume 1: "PROP P" and 2: "PROP Q"
  { assume *: "PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP R"
    show "PROP R" by (fact *[OF 1 2]) }
  { assume *: "PROP Q \<Longrightarrow> PROP P \<Longrightarrow> PROP R"
    show "PROP R" by (fact *[OF 2 1]) }
qed

lemma conjunction_IMP:
  "(PROP A &&& PROP B IMP PROP C) \<equiv> (PROP B IMP PROP A IMP PROP C)"
  by (simp add: IMP_def conjunction_imp swap_imp)

ML \<open>
fun imp_len tm =
  let
    val tm' = case tm of
        Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, body) => body
      | _ => tm
  in
    case tm' of
      Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ consequent => imp_len consequent + 1
    | _ => 0
  end

fun unconj_tac ctxt = SUBGOAL (fn (goal, i) =>
  (@{print} goal; @{print} (imp_len goal);
  compose_tac ctxt (false, @{thm conjunction_IMP}, 1) i))

fun subgoal_tac ctxt =
  Subgoal.FOCUS_PREMS (fn {context = goal_ctxt, params, prems, concl, ...} =>
    let
      
    in
      @{print} params;
      @{print} prems;
      @{print} concl;
      all_tac
    end
  ) ctxt

fun idind_tac fref tm ctxt =
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

method_setup unconj = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (HEADGOAL (unconj_tac ctxt)))\<close>

method_setup "subgoal" = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (HEADGOAL (subgoal_tac ctxt)))\<close>

method_setup idind = \<open>
  Scan.lift Parse.thm --
  Scan.option (Scan.lift (Args.$$$ "pred" -- Args.colon) |-- Args.term)
  >> (fn ((fref, _), tm) => fn ctxt => SIMPLE_METHOD (HEADGOAL (idind_tac fref tm ctxt)))
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
  by (congs; easy?) (reduce facts: assms)+

lemma funcomp_comp [reds]:
  assumes
    "\<And>x. x: A \<Longrightarrow> b x: B"
    "\<And>x. x: B \<Longrightarrow> c x: C x"
    "A: U"
  shows
    "(\<lambda>x: B. c x) \<circ>\<^bsub>A\<^esub> (\<lambda>x: A. b x) \<equiv> \<lambda>x: A. c (b x)"
  unfolding funcomp_def
  by (congs; easy?) (reduce facts: assms | routine facts: assms)+

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
  apply (rule IdE[of _ _ x y]; (fact+)?)
  apply (forms; (easy facts: assms))
  apply (intros; easy)
  done

definition "inv A x y p \<equiv> IdInd A (\<lambda>x y _. (y =\<^bsub>A\<^esub> x)) (\<lambda>x. refl x) x y p"

lemma Id_symmetric [elims, intros]:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "x: A" "y: A" "A: U"
  shows
    "inv A x y p: y =\<^bsub>A\<^esub> x"
  unfolding inv_def by (routine facts: assms)

lemma inv_comp [reds]:
  assumes
    "x: A" "A: U"
  shows
    "inv A x x (refl x) \<equiv> refl x"
  unfolding inv_def by reduce (routine facts: assms)

schematic_goal Id_transitive_derivation:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
    "A: U" "x: A" "y: A" "z: A"
  shows
    "?prf: x =\<^bsub>A\<^esub> z"
  (* Idea: change x to y in all statements. then change y to z. *)
  apply (rule IdE[of p A x y "\<lambda>x y p. (z: A &&& q: y =\<^bsub>A\<^esub> z)"];
        (elim elim_imp_to_IMP,
        (simp add: conjunction_IMP)?,
        simp add: IMP_def,
        elim elim_imp_to_IMP,
        simp add: IMP_def)?)
  apply (routine, (easy facts: assms)+)
  apply (elim elim_imp_to_IMP)
  apply (simp add: conjunction_IMP)
  (*
    Here we want to be able to do a nested induction.
    Need a custom subgoal tactic here that keeps the schematic variable!
  *)
  apply (simp only: IMP_def)
  done

definition "pathcomp A x y z p q \<equiv>
  (IdInd A
    (\<lambda>x y _. \<Prod>z: A. y =\<^bsub>A\<^esub> z \<rightarrow> x =\<^bsub>A\<^esub> z)
    (\<lambda>x. \<lambda>z: A. \<lambda>q: x =\<^bsub>A\<^esub> z. q)
    x y p) `z `q"
  (* IdInd A (\<lambda>x z _. (x =\<^bsub>A\<^esub> z)) (\<lambda>x. refl x) x z q *)

lemma Id_transitive [elims, intros]:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
    "A: U" "x: A" "y: A" "z: A"
  shows
    "pathcomp A x y z p q: x =\<^bsub>A\<^esub> z"
  unfolding pathcomp_def by (routine facts: assms)


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
  unfolding snd_def by (routine facts: assms | reduce)+

lemma snd_of_pair [reds]:
  assumes "A: U" "\<And>x. x: A \<Longrightarrow> B x: U" "a: A" "b: B a"
  shows "snd A B <a, b> \<equiv> b"
  unfolding snd_def by (routine facts: assms | reduce)+


end
