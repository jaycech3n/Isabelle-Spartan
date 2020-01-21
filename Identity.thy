chapter \<open>The identity type\<close>

text \<open>
  More about the identity type, the higher groupoid structure of types, and type
  families as fibrations.
\<close>

theory Identity
imports Implicits

begin

section \<open>Basic propositional equalities\<close>

(*TODO: Better integration of equality type directly into reasoning...*)

named_theorems eqs \<comment>\<open>For propositional equalities\<close>

schematic_goal pathcomp_left_refl_derivation:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: (refl x) \<bullet> p = p"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

schematic_goal pathcomp_right_refl [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: p \<bullet> (refl y) = p"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

schematic_goal pathcomp_left_inv [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: p\<inverse> \<bullet> p = refl y"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

schematic_goal pathcomp_right_inv [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: p \<bullet> p\<inverse> = refl x"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

schematic_goal pathinv_pathinv [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: p\<inverse>\<inverse> = p"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

text \<open>
  Associativity of path composition can be proved by a triply-nested path
  induction, which we do here. It can also be proved using functoriality of
  functions, which we'll do later.
\<close>

schematic_goal pathcomp_assoc:
  assumes
    "A: U i" "x: A" "y: A" "z: A" "w: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z" "r: z =\<^bsub>A\<^esub> w"
  shows "?prf: p \<bullet> (q \<bullet> r) = p \<bullet> q \<bullet> r"
  apply (equality \<open>p:_\<close>)
    schematic_subgoal premises for x q
      apply (equality \<open>q:_\<close>)
        schematic_subgoal premises for x r
          apply (equality \<open>r:_\<close>)
            apply (reduce; intros+)
        done
    done
  done


section \<open>Functoriality of functions\<close>

schematic_goal Id_transfer_derivation:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: f `x = f `y"
  apply (equality \<open>p: _\<close>)
    apply (intros; elims)
  done

definition "ap A B x y f p \<equiv>
  IdInd A (\<lambda>x y _. f `x =\<^bsub>B\<^esub> f `y) (\<lambda>x. refl (f `x)) x y p"

definition ap_i ("_[_]" [1000, 0])
  where [implicit]: "ap_i f p \<equiv> ap ? ? ? ? f p"

translations "f[p]" \<leftharpoondown> "CONST ap A B x y f p"

schematic_goal Id_transfer [typechk]:
  assumes
    "A: U i" "B: U i" "f: A \<rightarrow> B"
    "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "f[p]: f `x = f `y"
  unfolding ap_def by typechk

schematic_goal ap_refl [comps]:
  assumes "f: A \<rightarrow> B" "x: A" "A: U i" "B: U i"
  shows "f[refl x] \<equiv> refl (f `x)"
  unfolding ap_def by (subst comps) reduce

schematic_goal ap_pathcomp_derivation:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A" "z: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows
    "?prf: f[p \<bullet> q] = f[p] \<bullet> f[q]"
  apply (equality \<open>p:_\<close>)
    schematic_subgoal premises for x q
      apply (equality \<open>q:_\<close>)
        apply reduce
          apply intros+
            apply elims
    done
  done

definition "ap_pathcomp A B x y z f p q \<equiv> IdInd A
  (\<lambda>a b c. \<Prod>x: b =\<^bsub>A\<^esub> z.
    ap A B a z f (pathcomp A a b z c x) =\<^bsub>f `a =\<^bsub>B\<^esub> f `z\<^esub>
      pathcomp B (f `a) (f `b) (f `z) (ap A B a b f c) (ap A B b z f x))
  (\<lambda>x. \<lambda>xa: x =\<^bsub>A\<^esub> z.
    IdInd A
      (\<lambda>a b c. ap A B a b f (pathcomp A a a b (refl a) c) =\<^bsub>f `a =\<^bsub>B\<^esub> f `b\<^esub>
        pathcomp B (f `a) (f `a) (f `b) (ap A B a a f (refl a)) (ap A B a b f c))
      (\<lambda>a. refl (refl (f `a)))
      x z xa)
  x y p `q"

schematic_goal ap_pathcomp [typechk]:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A" "z: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows "ap_pathcomp A B x y z f p q: f[p \<bullet> q] = f[p] \<bullet> f[q]"
  unfolding ap_pathcomp_def by typechk reduce

schematic_goal ap_pathinv_derivation:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: f[p\<inverse>] = f[p]\<inverse>"
  by (equality \<open>p:_\<close>) (reduce, intros, typechk)

definition "ap_pathinv A B x y f p \<equiv> IdInd A
  (\<lambda>a b c. ap A B b a f (pathinv A a b c) =\<^bsub>f `b =\<^bsub>B\<^esub> f `a\<^esub>
    pathinv B (f `a) (f `b) (ap A B a b f c))
  (\<lambda>x. refl (refl (f `x)))
  x y p"

schematic_goal ap_pathinv [typechk]:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y"
  shows "ap_pathinv A B x y f p: f[p\<inverse>] = f[p]\<inverse>"
  unfolding ap_pathinv_def by typechk reduce

text \<open>The next two proofs currently use some low-level rewriting.\<close>

schematic_goal ap_funcomp_derivation:
  assumes
    "A: U i" "B: U i" "C: U i"
    "x: A" "y: A" "z: A"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: (g \<circ> f)[p] = g[f[p]]"
  apply (equality \<open>p:_\<close>)
    apply (simp only: funcomp_apply_comp[symmetric])
    apply (reduce, intros, typechk)
  done

definition "ap_funcomp A B C x y z f g p \<equiv> IdInd A
  (\<lambda>a b c. ap A C a b (g \<circ>\<^bsub>A\<^esub> f) c =\<^bsub>g `(f `a) =\<^bsub>C\<^esub> g `(f `b)\<^esub>
    ap B C (f `a) (f `b) g (ap A B a b f c))
  (\<lambda>x. refl (refl (g `(f `x))))
  x y p"

schematic_goal ap_funcomp [typechk]:
  assumes
    "A: U i" "B: U i" "C: U i"
    "x: A" "y: A" "z: A"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
    "p: x =\<^bsub>A\<^esub> y"
  shows "ap_funcomp A B C x y z f g p: (g \<circ> f)[p] = g[f[p]]"
  unfolding ap_funcomp_def by (rule ap_funcomp_derivation assms)+

schematic_goal ap_id_derivation:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: (id A)[p] = p"
  apply (equality \<open>p:_\<close>)
    schematic_subgoal for x y p
      apply (subst (6 8) id_comp[symmetric]; typechk)
    done
    apply (reduce; intros+)
  done

definition "ap_id A x y p \<equiv> IdInd A
  (\<lambda>a b c. ap A A a b (id A) c =\<^bsub>a =\<^bsub>A\<^esub> b\<^esub> c)
  (\<lambda>x. refl (refl x))
  x y p"

schematic_goal ap_id [typechk]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "ap_id A x y p: (id A)[p] = p"
  unfolding ap_id_def by (rule ap_id_derivation)


section \<open>Transport\<close>

schematic_goal transport_derivation:
  assumes
    "A: U i"
    "x: A" "y: A"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: P x \<rightarrow> P y"
  by (equality \<open>p:_\<close>) intros

definition "transport A x y P p \<equiv>
  IdInd A (\<lambda>a b _. P a \<rightarrow> P b) (\<lambda>x. \<lambda>u: P x. u) x y p"

definition transport_i ("trans")
  where [implicit]: "trans P p \<equiv> transport ? ? ? P p"

translations "trans P p" \<leftharpoondown> "CONST transport A x y P p"

schematic_goal transport [typechk]:
  assumes
    "A: U i"
    "x: A" "y: A"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "p: x =\<^bsub>A\<^esub> y"
  shows "trans P p: P x \<rightarrow> P y"
  unfolding transport_def by typechk

schematic_goal transport_comp [comps]:
  assumes
    "a: A"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
  shows "trans P (refl a) \<equiv> id (P a)"
  unfolding transport_def id_def by (subst comps) reduce

schematic_goal transport_left_inv [eqs]:
  assumes
    "A: U i"
    "x: A" "y: A"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: (trans P p\<inverse>) \<circ> (trans P p) = id (P x)"
  by (equality \<open>p:_\<close>) (reduce, intros, typechk)

schematic_goal transport_right_inv [eqs]:
  assumes
    "A: U i"
    "x: A" "y: A"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: (trans P p) \<circ> (trans P p\<inverse>) = id (P y)"
  by (equality \<open>p:_\<close>) (reduce, intros, typechk)

no_translations
  "x = y" \<leftharpoondown> "x =\<^bsub>A\<^esub> y"
  "trans P p" \<leftharpoondown> "CONST transport A x y P p"

schematic_goal pathlift_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: <x, u> = <y, trans P p u>"
  by (equality \<open>p:_\<close>) (reduce, intros, typechk)

definition "pathlift A x y P p u \<equiv> IdInd A
  (\<lambda>a b c. \<Prod>x: P a. <a, x> =\<^bsub>\<Sum>x: A. P x\<^esub> <b, transport A a b P c `x>)
  (\<lambda>x. \<lambda>xa: P x. refl <x, xa>)
  x y p `u"

definition pathlift_i ("lift")
  where [implicit]: "lift P p u \<equiv> pathlift ? ? ? P p u"

schematic_goal pathlift [typechk]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "lift P p u: <x, u> = <y, trans P p u>"
  unfolding pathlift_def by reduce+

ML \<open>
fun ttac ctxt =
  let val net = Tactic.build_net
    ((Named_Theorems.get ctxt \<^named_theorems>\<open>typechk\<close>)
    @(Named_Theorems.get ctxt \<^named_theorems>\<open>intros\<close>)
    @(Named_Theorems.get ctxt \<^named_theorems>\<open>elims\<close>))
  in
    known_tac ctxt ORELSE' resolve_from_net_tac ctxt net
  end
\<close>

schematic_goal pathlift_comp [comps]:
  assumes
    "u: P x"
    "x: A"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "A: U i"
  shows "lift P (refl x) u \<equiv> refl <x, u>"
  unfolding pathlift_def by (subst comps) reduce+

schematic_goal pathlift_fst_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: ?"
oops


end
