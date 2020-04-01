chapter \<open>The identity type\<close>

text \<open>
  More about the identity type, the higher groupoid structure of types, and type
  families as fibrations.
\<close>

theory Identity
imports Spartan Pair

begin

section \<open>Notation\<close>

definition Id_i (infix "=" 110)
  where [implicit]: "Id_i x y \<equiv> x =\<^bsub>?\<^esub> y"

definition pathinv_i ("_\<inverse>" [1000])
  where [implicit]: "pathinv_i p \<equiv> pathinv ? ? ? p"

definition pathcomp_i (infixl "\<bullet>" 121)
  where [implicit]: "pathcomp_i p q \<equiv> pathcomp ? ? ? ? p q"

translations
  "x = y" \<leftharpoondown> "x =\<^bsub>A\<^esub> y"
  "p\<inverse>" \<leftharpoondown> "CONST pathinv A x y p"
  "p \<bullet> q" \<leftharpoondown> "CONST pathcomp A x y z p q"


section \<open>Basic propositional equalities\<close>

(*TODO: Better integration of equality type directly into reasoning...*)

Lemma (derive) pathcomp_left_refl:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "(refl x) \<bullet> p = p"
  apply (equality \<open>p:_\<close>)
    apply (reduce; intros)
  done

Lemma (derive) pathcomp_right_refl:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "p \<bullet> (refl y) = p"
  apply (equality \<open>p:_\<close>)
    apply (reduce; intros)
  done

Lemma (derive) pathcomp_left_inv:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "p\<inverse> \<bullet> p = refl y"
  apply (equality \<open>p:_\<close>)
    apply (reduce; intros)
  done

Lemma (derive) pathcomp_right_inv:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "p \<bullet> p\<inverse> = refl x"
  apply (equality \<open>p:_\<close>)
    apply (reduce; intros)
  done

Lemma (derive) pathinv_pathinv:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "p\<inverse>\<inverse> = p"
  apply (equality \<open>p:_\<close>)
    apply (reduce; intros)
  done

Lemma (derive) pathcomp_assoc:
  assumes
    "A: U i" "x: A" "y: A" "z: A" "w: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z" "r: z =\<^bsub>A\<^esub> w"
  shows "p \<bullet> (q \<bullet> r) = p \<bullet> q \<bullet> r"
  apply (equality \<open>p:_\<close>)
    focus premises vars x p
      apply (equality \<open>p:_\<close>)
        focus premises vars x p
          apply (equality \<open>p:_\<close>)
            apply (reduce; intros)
        done
    done
  done


section \<open>Functoriality of functions\<close>

Lemma (derive) ap:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y"
  shows "f x = f y"
  apply (equality \<open>p:_\<close>)
    apply intro
  done

definition ap_i ("_[_]" [1000, 0])
  where [implicit]: "ap_i f p \<equiv> ap ? ? ? ? f p"

translations "f[p]" \<leftharpoondown> "CONST ap A B x y f p"

Lemma ap_refl [comps]:
  assumes "f: A \<rightarrow> B" "x: A" "A: U i" "B: U i"
  shows "f[refl x] \<equiv> refl (f x)"
  unfolding ap_def by reduce

Lemma (derive) ap_pathcomp:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A" "z: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows
    "f[p \<bullet> q] = f[p] \<bullet> f[q]"
  apply (equality \<open>p:_\<close>)
    focus premises vars x p
      apply (equality \<open>p:_\<close>)
        apply (reduce; intro)
    done
  done

Lemma (derive) ap_pathinv:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B"
    "p: x =\<^bsub>A\<^esub> y"
  shows "f[p\<inverse>] = f[p]\<inverse>"
  by (equality \<open>p:_\<close>) (reduce; intro)

text \<open>The next two proofs currently use some low-level rewriting.\<close>

Lemma (derive) ap_funcomp:
  assumes
    "A: U i" "B: U i" "C: U i"
    "x: A" "y: A"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
    "p: x =\<^bsub>A\<^esub> y"
  shows "(g \<circ> f)[p] = g[f[p]]"
  apply (equality \<open>p:_\<close>)
    apply (simp only: funcomp_apply_comp[symmetric])
    apply (reduce; intro)
  done

Lemma (derive) ap_id:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "(id A)[p] = p"
  apply (equality \<open>p:_\<close>)
    apply (rewrite at "\<hole> = _" id_comp[symmetric])
    apply (rewrite at "_ = \<hole>" id_comp[symmetric])
    apply (reduce; intros)
  done


section \<open>Transport\<close>

Lemma (derive) transport:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "P x \<rightarrow> P y"
  by (equality \<open>p:_\<close>) intro

definition transport_i ("trans")
  where [implicit]: "trans P p \<equiv> transport ? P ? ? p"

translations "trans P p" \<leftharpoondown> "CONST transport A P x y p"

Lemma transport_comp [comps]:
  assumes
    "a: A"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
  shows "trans P (refl a) \<equiv> id (P a)"
  unfolding transport_def id_def by reduce

\<comment> \<open>TODO: Build transport automation!\<close>

Lemma use_transport:
  assumes
    "p: y =\<^bsub>A\<^esub> x"
    "u: P x"
    "x: A" "y: A"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
  shows "trans P p\<inverse> u: P y"
  by typechk

Lemma (derive) transport_left_inv:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "(trans P p\<inverse>) \<circ> (trans P p) = id (P x)"
  by (equality \<open>p:_\<close>) (reduce; intro)

Lemma (derive) transport_right_inv:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "(trans P p) \<circ> (trans P p\<inverse>) = id (P y)"
  by (equality \<open>p:_\<close>) (reduce; intros)

Lemma (derive) transport_pathcomp:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A" "z: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows "trans P q (trans P p u) = trans P (p \<bullet> q) u"
  apply (equality \<open>p:_\<close>)
    focus premises vars x p
      apply (equality \<open>p:_\<close>)
        apply (reduce; intros)
    done
  done

Lemma (derive) transport_compose_typefam:
  assumes
    "A: U i" "B: U i"
    "\<And>x. x: B \<Longrightarrow> P x: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
    "u: P (f x)"
  shows "trans (\<lambda>x. P (f x)) p u = trans P f[p] u"
  by (equality \<open>p:_\<close>) (reduce; intros)

Lemma (derive) transport_function_family:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "\<And>x. x: A \<Longrightarrow> Q x: U i"
    "f: \<Prod>x: A. P x \<rightarrow> Q x"
    "x: A" "y: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "trans Q p ((f x) u) = (f y) (trans P p u)"
  by (equality \<open>p:_\<close>) (reduce; intros)

Lemma (derive) transport_const:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "\<Prod>b: B. trans (\<lambda>_. B) p b = b"
  by (intro, equality \<open>p:_\<close>) (reduce; intro)

definition transport_const_i ("trans'_const")
  where [implicit]: "trans_const B p \<equiv> transport_const ? B ? ? p"

translations "trans_const B p" \<leftharpoondown> "CONST transport_const A B x y p"

Lemma transport_const_comp [comps]:
  assumes
    "x: A" "b: B"
    "A: U i" "B: U i"
  shows "trans_const B (refl x) b\<equiv> refl b"
  unfolding transport_const_def by reduce

Lemma (derive) pathlift:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
    "u: P x"
  shows "<x, u> = <y, trans P p u>"
  by (equality \<open>p:_\<close>) (reduce; intros)

definition pathlift_i ("lift")
  where [implicit]: "lift P p u \<equiv> pathlift ? P ? ? p u"

translations "lift P p u" \<leftharpoondown> "CONST pathlift A P x y p u"

Lemma pathlift_comp [comps]:
  assumes
    "u: P x"
    "x: A"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "A: U i"
  shows "lift P (refl x) u \<equiv> refl <x, u>"
  unfolding pathlift_def by reduce

Lemma (derive) pathlift_fst:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "x: A" "y: A"
    "u: P x"
    "p: x =\<^bsub>A\<^esub> y"
  shows "fst[lift P p u] = p"
  apply (equality \<open>p:_\<close>)
    text \<open>Some rewriting needed here:\<close>
    \<guillemotright> vars x y
      (*Here an automatic reordering tactic would be helpful*)
      apply (rewrite at x in "x = y" fst_comp[symmetric])
        prefer 4
        apply (rewrite at y in "_ = y" fst_comp[symmetric])
      done
    \<guillemotright> by reduce intro
  done


section \<open>Dependent paths\<close>

Lemma (derive) apd:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
    "f: \<Prod>x: A. P x"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "trans P p (f x) = f y"
  by (equality \<open>p:_\<close>) (reduce; intros; typechk)

definition apd_i ("apd")
  where [implicit]: "apd f p \<equiv> Identity.apd ? ? f ? ? p"

translations "apd f p" \<leftharpoondown> "CONST Identity.apd A P f x y p"

Lemma dependent_map_comp [comps]:
  assumes
    "f: \<Prod>x: A. P x"
    "x: A"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> P x: U i"
  shows "apd f (refl x) \<equiv> refl (f x)"
  unfolding apd_def by reduce

Lemma (derive) apd_ap:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "apd f p = trans_const B p (f x) \<bullet> f[p]"
  by (equality \<open>p:_\<close>) (reduce; intro)

end
