chapter \<open>The identity type\<close>

text \<open>More about the identity type; the higher groupoid structure of types.\<close>

theory Identity
imports Implicits

begin

section \<open>Basic propositional equalities\<close>

(*TODO: Better integration of equality type directly into reasoning...*)

named_theorems eqs \<comment>\<open>For propositional equalities\<close>

schematic_goal pathcomp_left_refl [eqs]:
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
  assumes "A: U i" "x: A" "y: A" "p: y =\<^bsub>A\<^esub> x"
  shows "?prf: p\<inverse> \<bullet> p = refl x"
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
    "A: U i" "B: U i" "f: A \<rightarrow> B"
    "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: f `x = f `y"
  apply (equality \<open>p: _\<close>)
    apply (intros; elims)
  done

definition "ap A B f x y p \<equiv>
  IdInd A (\<lambda>x y _. f `x =\<^bsub>B\<^esub> f `y) (\<lambda>x. refl (f `x)) x y p"

definition ap_i ("_[_]" [1000, 0])
  where [implicit]: "ap_i f p \<equiv> ap {A} {B} f {x} {y} p"

translations "f[p]" \<leftharpoondown> "CONST ap A B f x y p"

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
    "f: A \<rightarrow> B"
    "x: A" "y: A" "z: A"
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

definition "ap_pathcomp A B f x y z p q \<equiv> IdInd A
  (\<lambda>a b c. \<Prod>x: b =\<^bsub>A\<^esub> z.
    ap A B f a z (pathcomp A a b z c x) =\<^bsub>f `a =\<^bsub>B\<^esub> f `z\<^esub>
      pathcomp B (f `a) (f `b) (f `z) (ap A B f a b c) (ap A B f b z x))
  (\<lambda>x. \<lambda>xa: x =\<^bsub>A\<^esub> z. IdInd A
    (\<lambda>a b c.
      ap A B f a b (pathcomp A a a b (refl a) c) =\<^bsub>f `a =\<^bsub>B\<^esub> f `b\<^esub>
        pathcomp B (f `a) (f `a) (f `b) (ap A B f a a (refl a)) (ap A B f a b c))
    (\<lambda>a. refl (refl (f `a)))
    x z xa)
  x y p `q"

schematic_goal ap_pathcomp [typechk]:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A" "z: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows "ap_pathcomp A B f x y z p q: f[p \<bullet> q] = f[p] \<bullet> f[q]"
  unfolding ap_pathcomp_def by typechk reduce

schematic_goal ap_pathinv_derivation:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: f[p\<inverse>] = f[p]\<inverse>"
  by (equality \<open>p:_\<close>) (reduce, intros, typechk)

definition "ap_pathinv A B f x y p \<equiv> IdInd A
  (\<lambda>a b c. ap A B f b a (pathinv A a b c) =\<^bsub>f `b =\<^bsub>B\<^esub> f `a\<^esub>
    pathinv B (f `a) (f `b) (ap A B f a b c))
  (\<lambda>x. refl (refl (f `x)))
  x y p"

schematic_goal ap_pathinv:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "ap_pathinv A B f x y p: f[p\<inverse>] = f[p]\<inverse>"
  unfolding ap_pathinv_def by reduce+

schematic_goal ap_funcomp_derivation:
  assumes
    "A: U i" "B: U i" "C: U i"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
    "x: A" "y: A" "z: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: (g \<circ> f)[p] = g[f[p]]"
  apply (equality \<open>p:_\<close>)
    apply (simp only: funcomp_apply_comp[symmetric])
    apply (reduce, intros, typechk)
  done

definition "ap_funcomp A B C f g x y z p \<equiv> IdInd A
  (\<lambda>a b c. ap A C (g \<circ>\<^bsub>A\<^esub> f) a b c =\<^bsub>(g \<circ>\<^bsub>A\<^esub> f) `a =\<^bsub>C\<^esub> (g \<circ>\<^bsub>A\<^esub> f) `b\<^esub>
    ap B C g (f `a) (f `b) (ap A B f a b c))
  (\<lambda>x. refl (refl (g `(f `x))))
  x y p"

schematic_goal ap_funcomp [typechk]:
  assumes
    "A: U i" "B: U i" "C: U i"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
    "x: A" "y: A" "z: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "ap_funcomp A B C f g x y z p: (g \<circ> f)[p] = g[f[p]]"
  unfolding ap_funcomp_def by reduce+

no_translations
  "x = y" \<leftharpoondown> "x =\<^bsub>A\<^esub> y"
  "g \<circ> f" \<leftharpoondown> "g \<circ>\<^bsub>A\<^esub> f"
  "(p)\<inverse>" \<leftharpoondown> "CONST pathinv A x y p"
  "(p \<bullet> q)" \<leftharpoondown> "CONST pathcomp A x y z p q"
  "f[p]" \<leftharpoondown> "CONST ap A B f x y p"

(*
  The following proof exposes two issues:

  1. Among the implicit arguments in the goal are x and y, which need to be
  modified by the equality method. But this cannot happen before the implicits
  are instantiated with their correct values!

  2. We might need to simplify under the dependent eliminator, and so need some
  kind of congruence rule here too.
*)
schematic_goal ap_id_derivation:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: ap A A (id A) x y p = p"
  apply (equality \<open>p:_\<close>)
    schematic_subgoal for x y p
      unfolding ap_def
      thm IdE[
        of p A x y,
        where ?C="\<lambda>x y _. id A `x =\<^bsub>A\<^esub> id A `y"
        and ?f="\<lambda>x. refl (id A `x)"]
oops


end
