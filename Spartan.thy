chapter \<open>Spartan type theory\<close>

theory Spartan
imports
  Pure
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"
keywords
  "print_coercions" :: thy_decl and
  "schematic_subgoal" "\<guillemotright>" :: prf_script_goal % "proof"

begin


section \<open>Preamble\<close>

declare [[eta_contract=false]]

ML_file \<open>schematic_subgoal.ML\<close>

ML_file \<open>$ISABELLE_HOME/src/Tools/subtyping.ML\<close>
declare [[coercion_enabled]]

named_theorems intros and elims and comps and typechk


section \<open>Metatype setup\<close>

typedecl o


section \<open>Judgments\<close>

axiomatization has_type :: \<open>o \<Rightarrow> o \<Rightarrow> prop\<close> ("(2_:/ _)")


section \<open>Universes\<close>

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

lemma U_in_U:
  "U i: U (S i)"
  by (rule U_hierarchy, rule lt_S)

lemma lift_universe:
  "A: U i \<Longrightarrow> A: U (S i)"
  by (erule U_cumulative, rule lt_S)


section \<open>\<Prod>-type\<close>

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
  PiF [intros]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> B x: U i; A: U i\<rbrakk> \<Longrightarrow> \<Prod>x: A. B x: U i" and

  PiI [intros]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x: B x; A: U i\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x: \<Prod>x: A. B x" and

  PiE [elims]: "\<lbrakk>f: \<Prod>x: A. B x; a: A\<rbrakk> \<Longrightarrow> f `a: B a" and

  beta [comps]: "\<lbrakk>a: A; \<And>x. x: A \<Longrightarrow> b x: B x\<rbrakk> \<Longrightarrow> (\<lambda>x: A. b x) `a \<equiv> b a" and

  eta: "f: \<Prod>x: A. B x \<Longrightarrow> \<lambda>x: A. f `x \<equiv> f" and

  Pi_cong [cong]: "\<lbrakk>
    A: U i;
    \<And>x. x: A \<Longrightarrow> B x: U i;
    \<And>x. x: A \<Longrightarrow> B' x: U i;
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x
    \<rbrakk> \<Longrightarrow> \<Prod>x: A. B x \<equiv> \<Prod>x: A. B' x" and

  lam_cong [cong]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b x \<equiv> c x; A: U i\<rbrakk> \<Longrightarrow> \<lambda>x: A. b x \<equiv> \<lambda>x: A. c x"


section \<open>\<Sum>-type\<close>

axiomatization
  Sig    :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o\<close> and
  pair   :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close> ("(2<_,/ _>)") and
  SigInd :: \<open>o \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o\<close>

syntax
  "_Sum" :: \<open>idt \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2\<Sum>_: _./ _)" 20)
translations
  "\<Sum>x: A. B" \<rightleftharpoons> "CONST Sig A (\<lambda>x. B)"

abbreviation Prod (infixl "\<times>" 50)
  where "A \<times> B \<equiv> \<Sum>_: A. B"

axiomatization where
  SigF [intros]: "\<lbrakk>\<And>x. x: A \<Longrightarrow> B x: U i; A: U i\<rbrakk> \<Longrightarrow> \<Sum>x: A. B x: U i" and

  SigI [intros]: "\<lbrakk>\<And>x. x : A \<Longrightarrow> B x: U i; a: A; b: B a\<rbrakk> \<Longrightarrow> <a, b>: \<Sum>x: A. B x" and

  SigE [elims]: "\<lbrakk>
    p: \<Sum>x: A. B x;
    A: U i;
    \<And>x. x : A \<Longrightarrow> B x: U i;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U i;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y>
    \<rbrakk> \<Longrightarrow> SigInd A B C f p: C p" and

  Sig_comp [comps]: "\<lbrakk>
    a: A;
    b: B a;
    \<And>x. x: A \<Longrightarrow> B x: U i;
    \<And>p. p: \<Sum>x: A. B x \<Longrightarrow> C p: U i;
    \<And>x y. \<lbrakk>x: A; y: B x\<rbrakk> \<Longrightarrow> f x y: C <x,y>
    \<rbrakk> \<Longrightarrow> SigInd A B C f <a, b> \<equiv> f a b" and

  Sig_cong [cong]: "\<lbrakk>
    \<And>x. x: A \<Longrightarrow> B x \<equiv> B' x;
    A: U i;
    \<And>x. x : A \<Longrightarrow> B x: U i;
    \<And>x. x : A \<Longrightarrow> B' x: U i
    \<rbrakk> \<Longrightarrow> \<Sum>x: A. B x \<equiv> \<Sum>x: A. B' x"


section \<open>Identity type\<close>

axiomatization
  Id    :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> and
  refl  :: \<open>o \<Rightarrow> o\<close> and
  IdInd :: \<open>o \<Rightarrow> (o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o) \<Rightarrow> (o \<Rightarrow> o) \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close>

syntax
  "_Id" :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2_ =\<^bsub>_\<^esub>/ _)" [111, 0, 111] 110)
translations
  "a =\<^bsub>A\<^esub> b" \<rightleftharpoons> "CONST Id A a b"

axiomatization where
  IdF [intros]: "\<lbrakk>A: U i; a: A; b: A\<rbrakk> \<Longrightarrow> a =\<^bsub>A\<^esub> b: U i" and

  IdI [intros]: "a: A \<Longrightarrow> refl a: a =\<^bsub>A\<^esub> a" and

  IdE [elims]: "\<lbrakk>
    p: a =\<^bsub>A\<^esub> b;
    a: A;
    b: A;
    \<And>x y p. \<lbrakk>p: x =\<^bsub>A\<^esub> y; x: A; y: A\<rbrakk> \<Longrightarrow> C x y p: U i;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x)
    \<rbrakk> \<Longrightarrow> IdInd A C f a b p: C a b p" and

  Id_comp [comps]: "\<lbrakk>
    a: A;
    \<And>x y p. \<lbrakk>x: A; y: A; p: x =\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> C x y p: U i;
    \<And>x. x: A \<Longrightarrow> f x: C x x (refl x)
    \<rbrakk> \<Longrightarrow> IdInd A C f a a (refl a) \<equiv> f a"


section \<open>Fundamental methods\<close>

ML_file \<open>lib.ML\<close>

\<comment>\<open>\<open>subst\<close> method\<close>
ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/eqsubst.ML"

ML \<open>
(*An assumption tactic that only solves typing subgoals with rigid terms and
  judgmental equalities without schematic variables*)
fun assumptions_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val concl = Logic.strip_assums_concl goal
  in
    if
      Lib.is_typing concl andalso Lib.is_rigid (Lib.term_of_typing concl)
      orelse not ((exists_subterm is_Var) concl)
    then assume_tac ctxt i
    else no_tac
  end)

(*Solves a typing subgoal with rigid term by unifying types and resolving with
  context facts and simplifier premises, or by *non-unifying* assumption*)
fun known_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val concl = Logic.strip_assums_concl goal
  in
    ((if Lib.is_typing concl andalso Lib.is_rigid (Lib.term_of_typing concl)
      then
        let val ths = map fst (Facts.props (Proof_Context.facts_of ctxt))
        in resolve_tac ctxt (ths @ Simplifier.prems_of ctxt) end
      else K no_tac)
    ORELSE' assumptions_tac ctxt) i
  end)

(*Applies some introduction rule*)
fun intros_tac ctxt = SUBGOAL (fn (_, i) =>
  (resolve_tac ctxt (Named_Theorems.get ctxt \<^named_theorems>\<open>intros\<close>)
  THEN_ALL_NEW (TRY o known_tac ctxt)) i)

(*Applies an elimination rule and solves the first resulting subgoal,
  which must be a typing judgment for the term being eliminated*)
fun elims_tac ctxt = SUBGOAL (fn (_, i) =>
  ((resolve_tac ctxt (Named_Theorems.get ctxt \<^named_theorems>\<open>elims\<close>)
    THEN' known_tac ctxt)
  THEN_ALL_NEW (TRY o known_tac ctxt)) i)

(*Typechecking: try to solve goals of the form "a: A" where a is rigid*)
fun typechk_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    fun rigid_typing_concl t =
      let val concl = Logic.strip_assums_concl t
      in Lib.is_typing concl andalso Lib.is_rigid (Lib.term_of_typing concl) end

    fun rtac ctxt = SUBGOAL (fn (goal, i) =>
      if rigid_typing_concl goal
      then
        let val net = Tactic.build_net
          ((Named_Theorems.get ctxt \<^named_theorems>\<open>typechk\<close>)
          @(Named_Theorems.get ctxt \<^named_theorems>\<open>intros\<close>)
          @(Named_Theorems.get ctxt \<^named_theorems>\<open>elims\<close>))
        in (resolve_from_net_tac ctxt net) i end
      else no_tac)
  in
    if rigid_typing_concl goal
    then (REPEAT_ALL_NEW (known_tac ctxt ORELSE' rtac ctxt)) i
    else no_tac
  end)

val auto_typechk = Attrib.setup_config_bool \<^binding>\<open>auto_typechk\<close> (K true)
\<close>

method_setup assumptions =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (
    CHANGED (TRYALL (assumptions_tac ctxt))))\<close>

method_setup known =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (
    CHANGED (TRYALL (known_tac ctxt))))\<close>

method_setup intros =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (HEADGOAL (intros_tac ctxt)))\<close>

method_setup elims =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (HEADGOAL (elims_tac ctxt)))\<close>

method_setup typechk =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (HEADGOAL (typechk_tac ctxt)))\<close>

method_setup rule =
  \<open>Attrib.thms >> (fn ths => fn ctxt =>
    let
      val sidecond_tac =
        if Config.get ctxt auto_typechk then typechk_tac else known_tac
    in
      SIMPLE_METHOD (HEADGOAL (
        resolve_tac ctxt ths
        THEN_ALL_NEW (TRY o sidecond_tac ctxt)))
    end)\<close>

\<comment>\<open>The Simplifier is used as a basis for some methods\<close>
setup \<open>
let
  fun solver_tac ctxt = REPEAT o CHANGED o typechk_tac ctxt
in
  map_theory_simpset (fn ctxt =>
    ctxt addSolver (mk_solver "" solver_tac))
end
\<close>

\<comment>\<open>Reduces terms via judgmental equalities\<close>
method reduce uses add = (simp add: comps add)


section \<open>Identity induction\<close>

ML_file \<open>equality.ML\<close>

method_setup equality = \<open>Scan.lift Parse.thm >> (fn (fact, _) => fn ctxt =>
  CONTEXT_METHOD (K (Equality.equality_context_tac fact ctxt)))\<close>


section \<open>Implicit arguments\<close>

text \<open>
  \<open>?\<close> is used to mark implicit arguments in definitions, while \<open>!\<close> is expanded
  immediately for elaboration in statements. 
\<close>

consts
  iarg :: \<open>'a\<close> ("?")
  earg :: \<open>'b\<close> ("!")

ML_file \<open>implicits.ML\<close>

attribute_setup implicit = \<open>Scan.succeed Implicits.implicit_defs_attr\<close>

ML \<open>
val _ = Context.>>
  (Syntax_Phases.term_check 1 "" (fn ctxt => map (Implicits.make_holes ctxt)))
\<close>


section \<open>Lambda coercion\<close>

\<comment>\<open>Coerce object lambdas to meta-lambdas when needed\<close>
abbreviation (input) lambda :: \<open>o \<Rightarrow> o \<Rightarrow> o\<close>
  where "lambda f \<equiv> \<lambda>x. f `x"

declare [[coercion lambda]]

translations "f x" \<leftharpoondown> "f `x"


section \<open>Functions\<close>

definition "funcomp A g f \<equiv> \<lambda>x: A. g `(f `x)"

syntax
  "_funcomp" :: \<open>o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o\<close> ("(2_ \<circ>\<^bsub>_\<^esub>/ _)" [111, 0, 110] 110)
translations
  "g \<circ>\<^bsub>A\<^esub> f" \<rightleftharpoons> "CONST funcomp A g f"

lemma funcompI [typechk]:
  assumes
    "A: U i"
    "B: U i"
    "\<And>x. x : B \<Longrightarrow> C x: U i"
    "f: A \<rightarrow> B"
    "g: \<Prod>x: B. C x"
  shows
    "g \<circ>\<^bsub>A\<^esub> f: \<Prod>x: A. C (f `x)"
  unfolding funcomp_def by typechk

lemma funcomp_assoc [comps]:
  assumes
    "f: A \<rightarrow> B"
    "g: B \<rightarrow> C"
    "h: \<Prod>x: C. D x"
    "A: U i"
  shows
    "(h \<circ>\<^bsub>B\<^esub> g) \<circ>\<^bsub>A\<^esub> f \<equiv> h \<circ>\<^bsub>A\<^esub> g \<circ>\<^bsub>A\<^esub> f"
  unfolding funcomp_def by reduce

lemma funcomp_lambda_comp [comps]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> b x: B"
    "\<And>x. x: B \<Longrightarrow> c x: C x"
  shows
    "(\<lambda>x: B. c x) \<circ>\<^bsub>A\<^esub> (\<lambda>x: A. b x) \<equiv> \<lambda>x: A. c (b x)"
  unfolding funcomp_def by reduce

lemma funcomp_apply_comp [comps]:
  assumes
    "f: A \<rightarrow> B" "g: \<Prod>x: B. C x"
    "x: A"
    "A: U i" "B: U i"
    "\<And>x y. x: B \<Longrightarrow> C x: U i"
  shows "(g \<circ>\<^bsub>A\<^esub> f) `x \<equiv> g `(f `x)"
  unfolding funcomp_def by reduce


definition id where "id A \<equiv> \<lambda>x: A. x"

lemma
  idI [typechk]: "A: U i \<Longrightarrow> id A: A \<rightarrow> A" and
  id_comp [comps]: "x: A \<Longrightarrow> (id A) `x \<equiv> x"
  unfolding id_def by reduce+

lemma id_left [comps]:
  assumes "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows "(id B) \<circ>\<^bsub>A\<^esub> f \<equiv> f"
  unfolding id_def
  by (subst eta[symmetric, of f], reduce+) (reduce add: eta)

lemma id_right [comps]:
  assumes "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows "f \<circ>\<^bsub>A\<^esub> (id A) \<equiv> f"
  unfolding id_def
  by (subst eta[symmetric, of f], reduce+) (reduce add: eta)

text \<open>Notation:\<close>

definition funcomp_i (infixr "\<circ>" 120)
  where [implicit]: "funcomp_i g f \<equiv> g \<circ>\<^bsub>?\<^esub> f"

translations "g \<circ> f" \<leftharpoondown> "g \<circ>\<^bsub>A\<^esub> f"

text \<open>Modus ponens; used in proofs.\<close>

lemma mp:
  assumes
    "A: U i" "B: U i"
    "a: A"
    "f: A \<rightarrow> B"
  shows "f `a: B"
  by typechk


section \<open>Equality\<close>

schematic_goal Id_symmetric_derivation:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: y =\<^bsub>A\<^esub> x"
  by (equality \<open>p:_\<close>) intros

(*TODO: automatically generate definitions for the terms derived in the above manner*)

definition "pathinv A x y p \<equiv> IdInd A (\<lambda>x y _. y =\<^bsub>A\<^esub> x) (\<lambda>x. refl x) x y p"

lemma Id_symmetric [typechk]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "pathinv A x y p: y =\<^bsub>A\<^esub> x"
  unfolding pathinv_def by typechk

lemma pathinv_comp [comps]:
  assumes "x: A" "A: U i"
  shows "pathinv A x x (refl x) \<equiv> refl x"
  unfolding pathinv_def by reduce

schematic_goal Id_transitive_derivation:
  assumes
    "A: U i" "x: A" "y: A" "z: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows
    "?prf: x =\<^bsub>A\<^esub> z"
  apply (equality \<open>p: _\<close>)
    schematic_subgoal premises for x q
      apply (equality \<open>q: _\<close>)
        apply intros
    done
  done

definition "pathcomp A x y z p q \<equiv>
  IdInd A
    (\<lambda>x y _. y =\<^bsub>A\<^esub> z \<rightarrow> x =\<^bsub>A\<^esub> z)
    (\<lambda>x. \<lambda>q: x =\<^bsub>A\<^esub> z. IdInd A (\<lambda>x z _. (x =\<^bsub>A\<^esub> z)) (\<lambda>x. refl x) x z q)
    x y p `q"

lemma Id_transitive [typechk]:
  assumes
    "A: U i" "x: A" "y: A" "z: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows
    "pathcomp A x y z p q: x =\<^bsub>A\<^esub> z"
  unfolding pathcomp_def by typechk

lemma pathcomp_comp [comps]:
  assumes "a: A" "A: U i"
  shows "pathcomp A a a a (refl a) (refl a) \<equiv> refl a"
  unfolding pathcomp_def by reduce


section \<open>Pairs\<close>

definition "fst A B \<equiv> \<lambda>p: \<Sum>x: A. B x. SigInd A B (\<lambda>_. A) (\<lambda>x y. x) p"
definition "snd A B \<equiv> \<lambda>p: \<Sum>x: A. B x. SigInd A B (\<lambda>p. B (fst A B p)) (\<lambda>x y. y) p"

lemma fst [typechk]:
  assumes "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "fst A B: (\<Sum>x: A. B x) \<rightarrow> A"
  unfolding fst_def by typechk

lemma fst_of_pair [comps]:
  assumes
    "a: A"
    "b: B a"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "fst A B <a, b> \<equiv> a"
  unfolding fst_def by reduce

lemma snd [typechk]:
  assumes "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "snd A B: \<Prod>p: \<Sum>x: A. B x. B (fst A B p)"
  unfolding snd_def by reduce+

lemma snd_of_pair [comps]:
  assumes "a: A" "b: B a" "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "snd A B <a, b> \<equiv> b"
  unfolding snd_def by reduce


section \<open>Types and universes\<close>

lemma lift_universe_codomain:
  assumes "A: U i" "f: A \<rightarrow> U i"
  shows "f: A \<rightarrow> U (S i)"
  apply (subst eta[symmetric])
    apply typechk
    apply intros
      apply (rule lift_universe)
  done


end
