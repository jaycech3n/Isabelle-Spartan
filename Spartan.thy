chapter \<open>Spartan type theory\<close>

theory Spartan
imports
  Pure
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"
keywords
  "schematic_subgoal" :: prf_script_goal % "proof" and
  "print_coercions" :: thy_decl

begin

declare [[names_short, eta_contract=false]]

ML_file \<open>schematic_subgoal.ML\<close>
ML_file \<open>subtyping.ML\<close>

named_theorems forms and intros and elims and decs and reds and congs


section \<open>Logical framework types\<close>

subsection \<open>Universe levels\<close>

class Lvl
default_sort Lvl

typedecl o
typedecl 'j T \<comment>\<open>akin to successor\<close>
typedecl ('i, 'j) V \<comment>\<open>universe joins\<close>

instance o   :: \<open>Lvl\<close> ..
instance T :: (\<open>Lvl\<close>) \<open>Lvl\<close> ..
instance V :: (\<open>Lvl\<close>, \<open>Lvl\<close>) \<open>Lvl\<close> ..


section \<open>Types & typing\<close>

subsection \<open>Judgments\<close>

consts has_type :: \<open>'i \<Rightarrow> 'i T \<Rightarrow> prop\<close> ("(2_:/ _)")

subsection \<open>Universes\<close>

axiomatization U :: \<open>'i T\<close>
axiomatization where hierarchy [forms]: "U: U"

subsection \<open>\<Prod>-type\<close>

axiomatization
  Pi  :: \<open>'i T \<Rightarrow> ('i \<Rightarrow> 'j T) \<Rightarrow> ('i, 'j) V T\<close> and
  lam :: \<open>'i T \<Rightarrow> ('i \<Rightarrow> 'j) \<Rightarrow> ('i, 'j) V\<close> and
  app :: \<open>('i, 'j) V \<Rightarrow> ('i, 'j) V \<Rightarrow> ('i, 'j) V\<close> ("(1_ `_)" [120, 121] 120)

syntax
  "_Pi"  :: \<open>pttrn \<Rightarrow> 'i T \<Rightarrow> 'j T \<Rightarrow> ('i, 'j) V\<close> ("(2\<Prod>_: _./ _)" 30)
  "_Fn"  :: \<open>'i T \<Rightarrow> 'j T \<Rightarrow> ('i, 'j) V\<close> (infixr "\<rightarrow>" 40)
  "_lam" :: \<open>pttrn \<Rightarrow> 'i T \<Rightarrow> 'j \<Rightarrow> ('i, 'j) V\<close> ("(2\<lambda>_: _./ _)" 30)
translations
  "\<Prod>x: A. B" \<rightleftharpoons> "CONST Pi A (\<lambda>x. B)"
  "A \<rightarrow> B" \<rightleftharpoons> "\<Prod>_: A. B"
  "\<lambda>x: A. b" \<rightleftharpoons> "CONST lam A (\<lambda>x. b)"

axiomatization where
  PiF [forms]: "\<lbrakk>A: U; \<And>x. x: A \<Longrightarrow> B x: U\<rbrakk> \<Longrightarrow> \<Prod>x: A. B x: U" and

  PiI [intros]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; A: U\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x: \<Prod>x: A. B x"

axiomatization where

  PiE [elims]: "\<lbrakk>f: \<Prod>x: A. B x; a: A\<rbrakk> \<Longrightarrow> f `a: B a"

(*
  Okay, this is a failed attempt. We need commutativity and associativity of the join
  operation, among other things. I need to encode universe levels deeply. *)

axiomatization where

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
  Sig    :: \<open>'i T \<Rightarrow> ('i \<Rightarrow> 'j T) \<Rightarrow> ('i, 'j) V T\<close> and
  pair   :: \<open>'i \<Rightarrow> 'j \<Rightarrow> ('i, 'j) V\<close> ("(2<_,/ _>)") and
  SigInd :: \<open>['i T, 'i \<Rightarrow> 'j T, ('i, 'j) V \<Rightarrow> 'k T, 'i \<Rightarrow> 'j \<Rightarrow>'k, ('i, 'j) V] \<Rightarrow> 'k\<close>

syntax
  "_Sum" :: \<open>[idt, 'i, 'j] \<Rightarrow> ('i, 'j) V T\<close> ("(2\<Sum>_: _./ _)" 20)
translations
  "\<Sum>x: A. B" \<rightleftharpoons> "CONST Sig A (\<lambda>x. B)"

abbreviation Cart (infixr "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_: A. B"

axiomatization where
  SigF [forms]: "\<lbrakk>A: U; \<And>x. x : A \<Longrightarrow> B x: U\<rbrakk> \<Longrightarrow> \<Sum>x: A. B x: U" and

  SigI [intros]: "\<lbrakk>a: A; b: B a; \<And>x. x : A \<Longrightarrow> B x: U\<rbrakk> \<Longrightarrow> <a, b>: \<Sum>x: A. B x" and

  SigE [elims]: "\<lbrakk>
    p: \<Sum>x: A. B x;
    A: U;
    \<And>x. x : A \<Longrightarrow> B x: U;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y>
    \<rbrakk> \<Longrightarrow> SigInd A B C f p: C p" and

  Sig_comp [reds]: "\<lbrakk>
    a: A;
    b: B a;
    \<And>x. x : A \<Longrightarrow> B x: U;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y>
    \<rbrakk> \<Longrightarrow> SigInd A B C f <a, b> \<equiv> f a b" and

  Sig_cong [congs]: "\<lbrakk>
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x;
    A: U;
    \<And>x. x : A \<Longrightarrow> B x: U;
    \<And>x. x : A \<Longrightarrow> B' x: U
    \<rbrakk> \<Longrightarrow> \<Sum>x: A. B x \<equiv> \<Sum>x: A. B' x"


subsection \<open>Identity type\<close>

axiomatization
  Id    :: \<open>['i T, 'i, 'i] \<Rightarrow> 'i T\<close> and
  refl  :: \<open>'i \<Rightarrow> 'i\<close> and
  IdInd :: \<open>['i T, ['i, 'i, 'i] \<Rightarrow> 'j T, 'i \<Rightarrow> 'j, 'i, 'i, 'i] \<Rightarrow> 'j\<close>

syntax
  "_Id" :: \<open>[_, 'i, _] \<Rightarrow> 'i\<close> ("(2_ =\<^bsub>_\<^esub>/ _)" [101, 0, 101] 100)
translations
  "a =\<^bsub>A\<^esub> b" \<rightleftharpoons> "CONST Id A a b"

axiomatization where
  IdF [forms]: "\<lbrakk>A: U; a: A; b: A\<rbrakk> \<Longrightarrow> a =\<^bsub>A\<^esub> b: U" and

  IdI [intros]: "a: A \<Longrightarrow> refl a: a =\<^bsub>A\<^esub> a" and

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

term "A =\<^bsub>U\<^esub> (A \<rightarrow> A)"

lemma
  assumes "A: U"
  shows "A =\<^bsub>U\<^esub> (A \<rightarrow> A): U"
oops

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

ML \<open>
(* Context assumptions that have already been pushed into the type family *)
structure Equality_Inserts = Proof_Data (
  type T = term Item_Net.T
  val init = K (Item_Net.init Term.aconv_untyped single)
)

local

(* Number of distinct subterms in `tms` that appear in `tm` *)
fun subterm_count tms tm = length (filter I (map (fn t => Lib.has_subterm [t] tm) tms))

fun push_hyp_tac t = Subgoal.FOCUS_PARAMS (fn {context = ctxt, concl, ...} =>
  let
    val (_, C) = Lib.dest_typing (Thm.term_of concl)
    val B = Thm.cterm_of ctxt (lambda t C)
    val a = Thm.cterm_of ctxt t
    (* The resolvent is PiE[where ?B=B and ?a=a] *)
    val resolvent = Drule.infer_instantiate' ctxt [NONE, NONE, SOME B, SOME a] @{thm PiE}
  in
    HEADGOAL (resolve_tac ctxt [resolvent])
    THEN SOMEGOAL (known_raw_tac ctxt)
  end)

fun induction_tac p A x y ctxt =
  let
    val [p, A, x, y] = map (Thm.cterm_of ctxt) [p, A, x, y]
  in
    HEADGOAL (resolve_tac ctxt
      [Drule.infer_instantiate' ctxt [SOME p, SOME A, SOME x, SOME y] @{thm IdE}])
  end

fun side_conds_tac ctxt =
  let
    val intros = Named_Theorems.get ctxt \<^named_theorems>\<open>intros\<close>
    val forms = Named_Theorems.get ctxt \<^named_theorems>\<open>forms\<close>
  in
    REPEAT o CHANGED o (known_raw_tac ctxt ORELSE' resolve_tac ctxt (intros @ forms))
  end

in

fun equality_context_tac fact ctxt =
  let
    val eq_th = Proof_Context.get_fact_single ctxt fact
    val (p, (A, x, y)) = (Lib.dest_typing ##> Lib.dest_Id) (Thm.prop_of eq_th)

    val hyps =
      Facts.props (Proof_Context.facts_of ctxt)
      |> map (Lib.dest_typing o Thm.prop_of o fst)
      |> filter_out (fn (t, _) =>
          Term.aconv (t, p) orelse Item_Net.member (Equality_Inserts.get ctxt) t)
      |> map (fn (t, T) => ((t, T), subterm_count [p, x, y] T))
      |> filter (fn (_, i) => i > 0)
      (*
        `t1: T1` comes before `t2: T2` if T1 contains t2 as subterm.
        If they are incomparable, then order by decreasing `subterm_count [p, x, y] T`.
      *)
      |> sort (fn (((t1, _), i), ((_, T2), j)) =>
          Lib.cond_order (Lib.subterm_order T2 t1) (int_ord (j, i)))
      |> map #1

    val record_inserts =
      Equality_Inserts.map (fold (fn (t, _) => fn net => Item_Net.update t net) hyps)

    val tac =
      fold (fn (t, _) => fn tac => tac THEN HEADGOAL (push_hyp_tac t ctxt)) hyps all_tac
      THEN (
        induction_tac p A x y ctxt
        THEN RANGE (replicate 3 (known_raw_tac ctxt) @ [side_conds_tac ctxt]) 1
      )
      THEN (
        REPEAT_DETERM_N (length hyps) (SOMEGOAL (resolve_tac ctxt @{thms PiI}))
        THEN ALLGOALS (side_conds_tac ctxt)
      )
  in
    fn (ctxt, st) => Method.CONTEXT (record_inserts ctxt) (tac st)
  end

end
\<close>

method_setup equality =
  \<open>Scan.lift Parse.thm >> (fn (fact, _) => fn ctxt =>
    CONTEXT_METHOD (K (equality_context_tac fact ctxt)))\<close>


section \<open>Functions\<close>

subsection \<open>Composition\<close>

definition funcomp
  where "funcomp A g f \<equiv> \<lambda>x: A. g `(f `x)"

term funcomp

syntax
  "_funcomp" :: \<open>_ \<Rightarrow> 'i \<Rightarrow> _ \<Rightarrow> _\<close> (* :: \<open>[('b, 'c) Pi, 'a T, ('a, 'b) Pi] \<Rightarrow> ('a, 'c) Pi\<close> *) ("(2_ \<circ>\<^bsub>_\<^esub>/ _)" [111, 0, 110] 110)
translations
  "g \<circ>\<^bsub>A\<^esub> f" \<rightleftharpoons> "CONST funcomp A g f"

term "funcomp A g f"
term "g \<circ>\<^bsub>A\<^esub> f"

lemma funcompI:
  assumes
    "f: A \<rightarrow> B" and
    "g: \<Prod>x: B. C x" and
    "A: U" and
    "B: U" and
    "\<And>x. x : B \<Longrightarrow> C x: U"
  shows
    "g \<circ>\<^bsub>A\<^esub> f: \<Prod>x: A. C (f`x)"
  unfolding funcomp_def by routine

lemma funcomp_assoc:
  assumes
    "f: A \<rightarrow> B"
    "g: B \<rightarrow> C"
    "h: \<Prod>x: C. D x"
    "A: U"
  shows
    "(h \<circ>\<^bsub>B\<^esub> g) \<circ>\<^bsub>A\<^esub> f \<equiv> h \<circ>\<^bsub>A\<^esub> g \<circ>\<^bsub>A\<^esub> f"
  unfolding funcomp_def
  by (congs; known?) (reduce | routine)+

lemma funcomp_comp [reds]:
  assumes
    "\<And>x. x: A \<Longrightarrow> b x: B"
    "\<And>x. x: B \<Longrightarrow> c x: C x"
    "A: U"
  shows
    "(\<lambda>x: B. c x) \<circ>\<^bsub>A\<^esub> (\<lambda>x: A. b x) \<equiv> \<lambda>x: A. c (b x)"
  unfolding funcomp_def
  by (congs; known?) reduce+

subsection \<open>Identity function\<close>

definition id where "id A \<equiv> \<lambda>x: A. x"

lemma idI: "A: U \<Longrightarrow> id A: A \<rightarrow> A"
  and id_comp [reds]: "x: A \<Longrightarrow> (id A) `x \<equiv> x"
  unfolding id_def by (intros; known) reduce

lemma id_left [reds]:
  assumes
    "f: A \<rightarrow> B" "A: U" "B: U"
  shows
    "(id B) \<circ>\<^bsub>A\<^esub> f \<equiv> f"
  unfolding id_def
  by (subst eta[symmetric, of f]; known?) (reduce; (routine facts: eta)?)

lemma id_right [reds]:
  assumes
    "f: A \<rightarrow> B" "A: U" "B: U"
  shows
    "f \<circ>\<^bsub>A\<^esub> (id A) \<equiv> f"
  unfolding id_def
  by (subst eta[symmetric, of f]; known?) (reduce; (routine facts: eta)?)


section \<open>Identity\<close>

schematic_goal Id_symmetric_derivation:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "x: A" "y: A" "A: U"
  shows
    "?prf: y =\<^bsub>A\<^esub> x"
  by (equality \<open>p: _\<close>)

(* TODO: automatically generate definitions for the terms derived in the above manner. *)

definition "pathinv A x y p \<equiv> IdInd A (\<lambda>x y _. y =\<^bsub>A\<^esub> x) (\<lambda>x. refl x) x y p"

lemma Id_symmetric:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "x: A" "y: A" "A: U"
  shows
    "pathinv A x y p: y =\<^bsub>A\<^esub> x"
  unfolding pathinv_def by (rule Id_symmetric_derivation assms)+

lemma pathinv_comp [reds]:
  assumes
    "x: A" "A: U"
  shows
    "pathinv A x x (refl x) \<equiv> refl x"
  unfolding pathinv_def by reduce routine

schematic_goal Id_transitive_derivation:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
    "A: U" "x: A" "y: A" "z: A"
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
    "A: U" "x: A" "y: A" "z: A"
  shows
    "pathcomp A x y z p q: x =\<^bsub>A\<^esub> z"
  unfolding pathcomp_def by (rule Id_transitive_derivation assms)+

lemma pathcomp_comp [reds]:
  "\<lbrakk>A: U; a: A\<rbrakk> \<Longrightarrow> pathcomp A a a a (refl a) (refl a) \<equiv> refl a"
  unfolding pathcomp_def by (reduce | routine)+


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
  unfolding snd_def by (reduce | routine)+

lemma snd_of_pair [reds]:
  assumes "A: U" "\<And>x. x: A \<Longrightarrow> B x: U" "a: A" "b: B a"
  shows "snd A B <a, b> \<equiv> b"
  unfolding snd_def by (reduce | routine)+


end
