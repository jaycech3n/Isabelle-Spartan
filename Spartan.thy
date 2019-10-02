chapter \<open>Spartan type theory\<close>

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

named_theorems forms and intros and elims and decs and reds and congs


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

subsection \<open>Judgments\<close>

consts has_type :: \<open>['a, 'a Type] \<Rightarrow> prop\<close> ("(2_:/ _)")


subsection \<open>Universes\<close>

axiomatization U :: \<open>'a Type\<close>
axiomatization where hierarchy [forms]: "U: U"


subsection \<open>\<Prod>-type\<close>

axiomatization
  Pi :: \<open>['a Type, 'a \<Rightarrow> 'b Type] \<Rightarrow> ('a, 'b) Pi Type\<close> and
  lam  :: \<open>['a Type, 'a \<Rightarrow> 'b] \<Rightarrow> ('a, 'b) Pi\<close> and
  app  :: \<open>[('a, 'b) Pi, 'a] \<Rightarrow> 'b\<close> ("(1_ `_)" [120, 121] 120)

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


subsection \<open>Identity type\<close>

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

ML_file \<open>util.ML\<close>

ML \<open>Util.subterm_order @{term "T y"} @{term x}\<close>

ML \<open>
local

(* Number of distinct subterms in `tms` that appear in `tm` *)
fun subterm_count tms tm = length (filter I (map (fn t => Util.has_subterm [t] tm) tms))

in

(* Context assumptions that have already been pushed into the type family *)
structure Equality_Inserts = Proof_Data (
  type T = term Item_Net.T
  val init = K (Item_Net.init Term.aconv_untyped single)
)

(* Needs to be a context_tactic because we update the proof data above *)
fun equality_context_tac factref (ctxt, st) =
  let
    val eq_th = Proof_Context.get_fact_single ctxt factref
    val (p, (A, x, y)) = (Util.dest_typing ##> Util.dest_Id) (Thm.prop_of eq_th)

    val hyps =
      Facts.props (Proof_Context.facts_of ctxt)
      |> map (Util.dest_typing o Thm.prop_of o fst)
      |> filter_out (fn (t, _) =>
          Term.aconv (t, p) orelse Item_Net.member (Equality_Inserts.get ctxt) t)
      |> map (fn (t, T) => ((t, T), subterm_count [p, x, y] T))
      |> filter (fn (_, i) => i > 0)
      |> sort (fn (((t1, _), i), ((_, T2), j)) =>
          Util.cond_order (Util.subterm_order T2 t1) (int_ord (j, i)))
        (*
          ^ `t1: T1` comes before `t2: T2` if T1 contains t2 as subterm.
          If they are incomparable, then order by decreasing `subterm_count [p, x, y] T`.
        *)
      |> map #1

    val ctxt' = ctxt
      |> Equality_Inserts.map (fold (fn (t, _) => fn net => Item_Net.update t net) hyps)

    fun hyp_tac t ctxt = Subgoal.FOCUS_PARAMS (fn {context, concl, ...} =>
      let
        val (_, C) = Util.dest_typing (Thm.term_of concl)
        val B = Thm.cterm_of context (lambda t C)
        val a = Thm.cterm_of context t
        (* The resolvent is PiE[where ?B=B and ?a=a] *)
        val resolvent = Drule.infer_instantiate' context [NONE, NONE, SOME B, SOME a] @{thm PiE}
      in
        HEADGOAL (resolve_tac context [resolvent])
        THEN ALLGOALS (TRY o (known_raw_tac context))
      end) ctxt

    fun equality_tac ctxt = Subgoal.FOCUS_PREMS (fn {context, ...} =>
      let
        val push_hyps_tac =
          fold (fn (t, _) => fn tac => tac THEN HEADGOAL (hyp_tac t context)) hyps all_tac

        val pathind_tac =
          let
            val [p, A, x, y] = map (Thm.cterm_of context) [p, A, x, y]
          in
            HEADGOAL (resolve_tac context
              [Drule.infer_instantiate' context [SOME p, SOME A, SOME x, SOME y] @{thm IdE}])
          end

        val pull_hyps_tac = SUBGOAL (fn (_, i) =>
          REPEAT_DETERM_N (length hyps) (resolve_tac context @{thms PiI} i))

        fun side_conds_tac ths =
          known_raw_tac context
          ORELSE' (
            resolve_tac context ths
            THEN' (TRY o known_raw_tac context)
          )

        val forms = Named_Theorems.get context \<^named_theorems>\<open>forms\<close>
        val intros = Named_Theorems.get context \<^named_theorems>\<open>intros\<close>
      in
        (* Push the necessary Isar hypotheses into the type family *)
        push_hyps_tac

        (* Identity induction *)
        THEN (
          pathind_tac
          THEN ALLGOALS (TRY o REPEAT o (side_conds_tac forms))
        )

        (* Pull hypotheses back out into the Isar context *)
        THEN (
          SOMEGOAL pull_hyps_tac
          THEN ALLGOALS (TRY o REPEAT o (side_conds_tac (forms @ intros)))
        )
      end) ctxt
  in
    Seq.make_results (
      Seq.lift (fn st => fn ctxt => (ctxt, st)) (HEADGOAL (equality_tac ctxt) st) ctxt')
  end

end
\<close>

method_setup equality =
  \<open>Scan.lift Parse.thm >> (fn (factref, _) => fn ctxt =>
    CONTEXT_METHOD (K (equality_context_tac factref)))\<close>


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
