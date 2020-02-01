chapter \<open>The identity type\<close>

text \<open>
  More about the identity type, the higher groupoid structure of types, and type
  families as fibrations.
\<close>

theory Identity
imports Spartan

begin

section \<open>Basic propositional equalities\<close>

(*TODO: Better integration of equality type directly into reasoning...*)

schematic_goal pathcomp_left_refl_derivation:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: (refl x) \<bullet> p = p"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

definition "pathcomp_left_refl A x y p \<equiv>  IdInd A
  (\<lambda>x y p. pathcomp A x x y (refl x) p =\<^bsub>x =\<^bsub>A\<^esub> y\<^esub> p)
  (\<lambda>x. refl (refl x))
  x y p"

schematic_goal pathcomp_left_refl [typechk]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "pathcomp_left_refl A x y p: (refl x) \<bullet> p = p"
  unfolding pathcomp_left_refl_def by typechk reduce

schematic_goal pathcomp_right_refl_derivation:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: p \<bullet> (refl y) = p"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

definition "pathcomp_right_refl A x y p \<equiv> IdInd A
  (\<lambda>x y p. pathcomp A x y y p (refl y) =\<^bsub>x =\<^bsub>A\<^esub> y\<^esub> p)
  (\<lambda>x. refl (refl x))
  x y p"

schematic_goal pathcomp_right_refl [typechk]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "pathcomp_right_refl A x y p: p \<bullet> (refl y) = p"
  unfolding pathcomp_right_refl_def by typechk reduce

schematic_goal pathcomp_left_inv_derivation:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: p\<inverse> \<bullet> p = refl y"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

definition "pathcomp_left_inv A x y p \<equiv> IdInd A
  (\<lambda>a b p. pathcomp A b a b (pathinv A a b p) p =\<^bsub>b =\<^bsub>A\<^esub> b\<^esub> refl b)
  (\<lambda>x. refl (refl x)) x y p"

schematic_goal pathcomp_left_inv [typechk]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "pathcomp_left_inv A x y p: p\<inverse> \<bullet> p = refl y"
  unfolding pathcomp_left_inv_def by typechk reduce

schematic_goal pathcomp_right_inv_derivation:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: p \<bullet> p\<inverse> = refl x"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

definition "pathcomp_right_inv A x y p \<equiv> IdInd A
  (\<lambda>a b p. pathcomp A a b a p (pathinv A a b p) =\<^bsub>a =\<^bsub>A\<^esub> a\<^esub> refl a)
  (\<lambda>x. refl (refl x)) x y p"

schematic_goal pathcomp_right_inv [typechk]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "pathcomp_right_inv A x y p: p \<bullet> p\<inverse> = refl x"
  unfolding pathcomp_right_inv_def by typechk reduce

schematic_goal pathinv_pathinv_derivation:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: p\<inverse>\<inverse> = p"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

definition "pathinv_pathinv A x y p \<equiv> IdInd A
  (\<lambda>a b p. pathinv A b a (pathinv A a b p) =\<^bsub>a =\<^bsub>A\<^esub> b\<^esub> p)
  (\<lambda>x. refl (refl x)) x y p"

schematic_goal pathinv_pathinv [typechk]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "pathinv_pathinv A x y p: p\<inverse>\<inverse> = p"
  unfolding pathinv_pathinv_def by typechk reduce

schematic_goal pathcomp_assoc_derivation:
  assumes
    "A: U i" "x: A" "y: A" "z: A" "w: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z" "r: z =\<^bsub>A\<^esub> w"
  shows "?prf: p \<bullet> (q \<bullet> r) = p \<bullet> q \<bullet> r"
  apply (equality \<open>p:_\<close>)
    schematic_subgoal premises for x p
      apply (equality \<open>p:_\<close>)
        schematic_subgoal premises for x p
          apply (equality \<open>p:_\<close>)
            apply (reduce; intros+)
        done
    done
  done

definition "pathcomp_assoc A x y z w p q r \<equiv>
  (IdInd A
    (\<lambda>a b c. \<Prod>x: b =\<^bsub>A\<^esub> z.
      pathcomp A a b w c (pathcomp A b z w x r) =\<^bsub>a =\<^bsub>A\<^esub> w\<^esub>
        pathcomp A a z w (pathcomp A a b z c x) r)
    (\<lambda>x. \<lambda>xa: x =\<^bsub>A\<^esub> z.
      (IdInd A
        (\<lambda>a b c. \<Prod>x: b =\<^bsub>A\<^esub> w.
          pathcomp A a a w (refl a) (pathcomp A a b w c x) =\<^bsub>a =\<^bsub>A\<^esub> w\<^esub>
            pathcomp A a b w (pathcomp A a a b (refl a) c) x)
        (\<lambda>a. \<lambda>x: a =\<^bsub>A\<^esub> w.
          IdInd A
            (\<lambda>a b c. pathcomp A a a b (refl a) (pathcomp A a a b (refl a) c)
              =\<^bsub>a =\<^bsub>A\<^esub> b\<^esub> pathcomp A a a b (pathcomp A a a a (refl a) (refl a)) c)
            (\<lambda>a. refl (refl a)) a w x)
            x z xa) r) x y p) q"

schematic_goal pathcomp_assoc [typechk]:
  assumes
    "A: U i" "x: A" "y: A" "z: A" "w: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z" "r: z =\<^bsub>A\<^esub> w"
  shows "pathcomp_assoc A x y z w p q r: p \<bullet> (q \<bullet> r) = p \<bullet> q \<bullet> r"
  unfolding pathcomp_assoc_def by typechk reduce


section \<open>Functoriality of functions\<close>

schematic_goal Id_transfer_derivation:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: f `x = f `y"
  apply (equality \<open>p: _\<close>)
    apply (intros; typechk)
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
    schematic_subgoal premises for x p
      apply (equality \<open>p:_\<close>)
        apply (reduce; intros; typechk)
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
  by (equality \<open>p:_\<close>) (reduce; intros; typechk)

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
    apply (reduce; intros; typechk)
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
    apply (subst (6 8) id_comp[symmetric]; typechk)
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
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: P x \<rightarrow> P y"
  by (equality \<open>p:_\<close>) intros

definition "transport A P x y p \<equiv>
  IdInd A (\<lambda>a b _. P a \<rightarrow> P b) (\<lambda>x. \<lambda>u: P x. u) x y p"

definition transport_i ("trans")
  where [implicit]: "trans P p \<equiv> transport ? P ? ? p"

translations "trans P p" \<leftharpoondown> "CONST transport A P x y p"

schematic_goal transport [typechk]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
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

schematic_goal use_transport:
  assumes
    "p: x =\<^bsub>A\<^esub> y"
    "u: P y"
    "x: A" "y: A"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
  shows "trans P p\<inverse> u: P x"
  by typechk

text \<open>TODO: Build transport automation!\<close>

schematic_goal transport_left_inv_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: (trans P p\<inverse>) \<circ> (trans P p) = id (P x)"
  by (equality \<open>p:_\<close>) (reduce; intros; typechk)

schematic_goal transport_right_inv_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: (trans P p) \<circ> (trans P p\<inverse>) = id (P y)"
  by (equality \<open>p:_\<close>) (reduce; intros; typechk)

schematic_goal transport_pathcomp_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A" "z: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows "?prf: trans P q (trans P p u) = trans P (p \<bullet> q) u"
  apply (equality \<open>p:_\<close>)
    schematic_subgoal premises for x p
      apply (equality \<open>p:_\<close>)
        apply (reduce; intros)
    done
  done

schematic_goal transport_compose_typefam_derivation:
  assumes
    "A: U i" "B: U i"
    "\<And>x. x: B \<Longrightarrow> P x: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
    "u: P (f x)"
  shows "?prf: trans (\<lambda>x. P (f x)) p u = trans P f[p] u"
  by (equality \<open>p:_\<close>) (reduce; intros)

schematic_goal transport_function_family_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "\<And>x. x: A \<Longrightarrow> Q x: U i"
    "f: \<Prod>x: A. P x \<rightarrow> Q x"
    "x: A" "y: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: trans Q p ((f x) u) = (f y) (trans P p u)"
  by (equality \<open>p:_\<close>) (reduce; intros; typechk)

schematic_goal transport_const_derivation:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
    "b: B"
  shows "?prf: trans (\<lambda>_. B) p b = b"
  by (equality \<open>p:_\<close>) (reduce; intros)

definition "transport_const A B x y p \<equiv> \<lambda>b: B.
  IdInd A (\<lambda>x y p. transport A (\<lambda>_. B) x y p `b =\<^bsub>B\<^esub> b) (\<lambda>x. refl b) x y p"

definition transport_const_i ("trans'_const")
  where [implicit]: "trans_const B p \<equiv> transport_const ? B ? ? p"

translations "trans_const B p" \<leftharpoondown> "CONST transport_const A B x y p"

schematic_goal transport_const [typechk]:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "trans_const B p: \<Prod>b: B. trans (\<lambda>_. B) p b = b"
  unfolding transport_const_def by reduce+

schematic_goal transport_const_comp [comps]:
  assumes
    "A: U i" "B: U i"
    "x: A" "b: B"
  shows "trans_const B (refl x) b\<equiv> refl b"
  unfolding transport_const_def by (subst comps) reduce+

schematic_goal pathlift_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: <x, u> = <y, trans P p u>"
  by (equality \<open>p:_\<close>) (reduce; intros; typechk)

definition "pathlift A P x y p u \<equiv> IdInd A
  (\<lambda>a b c. \<Prod>x: P a. <a, x> =\<^bsub>\<Sum>x: A. P x\<^esub> <b, transport A P a b c `x>)
  (\<lambda>x. \<lambda>xa: P x. refl <x, xa>)
  x y p `u"

definition pathlift_i ("lift")
  where [implicit]: "lift P p u \<equiv> pathlift ? P ? ? p u"

translations "lift P p u" \<leftharpoondown> "CONST pathlift A P x y p u"

schematic_goal pathlift [typechk]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "lift P p u: <x, u> = <y, trans P p u>"
  unfolding pathlift_def by reduce+

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
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: fst[lift P p u] = p"
  apply (equality \<open>p:_\<close>)
    text \<open>Some rewriting needed here:\<close>
    schematic_subgoal for x y
      apply (subst fst_of_pair[where ?a=x, symmetric])
        prefer 5
        apply (subst fst_of_pair[where ?a=y, symmetric])
          prefer 5
          apply typechk+
    done
    apply (reduce; intros; typechk)
  done

definition "pathlift_fst A P x y p u \<equiv> IdInd A
  (\<lambda>a b c. \<Prod>x: P a. ap (\<Sum>x: A. P x) A <a, x> <b, transport A (\<lambda>a. P a) a b c `x>
    (Spartan.fst A (\<lambda>a. P a)) (pathlift A (\<lambda>a. P a) a b c x) =\<^bsub>a =\<^bsub>A\<^esub> b\<^esub> c)
  (\<lambda>x. \<lambda>_: P x. refl (refl x))
  x y p `u"

schematic_goal pathlift_fst:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "pathlift_fst A P x y p u: fst[lift P p u] = p"
  unfolding pathlift_fst_def by (rule pathlift_fst_derivation)


section \<open>Dependent paths\<close>

schematic_goal dependent_map_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "f: \<Prod>x: A. P x"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: trans P p (f` x) = f `y"
  by (equality \<open>p:_\<close>) (reduce; intros; typechk)

definition "apd A P f x y p \<equiv> IdInd A
  (\<lambda>x y p. transport A (\<lambda>x. P x) x y p `(f `x) =\<^bsub>P y\<^esub> f `y)
  (\<lambda>x. refl (f `x))
  x y p"

definition apd_i ("apd")
  where [implicit]: "apd f p \<equiv> Identity.apd ? ? f ? ? p"

translations "apd f p" \<leftharpoondown> "CONST Identity.apd A P f x y p"

schematic_goal dependent_map [typechk]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "f: \<Prod>x: A. P x"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "apd f p: trans P p (f` x) = f `y"
  unfolding apd_def by typechk reduce

schematic_goal dependent_map_comp [comps]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "f: \<Prod>x: A. P x"
    "x: A"
  shows "apd f (refl x) \<equiv> refl (f x)"
  unfolding apd_def by (subst comps) reduce+

schematic_goal apd_ap_derivation:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: apd f p = trans_const B p (f `x) \<bullet> f[p]"
  by (equality \<open>p:_\<close>) (reduce; intros; typechk)


end
