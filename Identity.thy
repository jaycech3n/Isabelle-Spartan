chapter \<open>The identity type\<close>

text \<open>More about the identity type; the higher groupoid structure of types.\<close>

theory Identity
imports Implicits

begin

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

definition [implicit]:
  "ap_i f p \<equiv> ap {A} {B} f {x} {y} p"

bundle ap_syntax begin
  notation ap_i ("_[_]" [1000, 0])
end

bundle no_ap_syntax begin
  no_notation ap_i ("_[_]" [1000, 0])
end

unbundle ap_syntax

schematic_goal Id_transfer [typechk]:
  assumes
    "A: U i" "B: U i" "f: A \<rightarrow> B"
    "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "f[p]: f `x = f `y"
  unfolding ap_def by typechk

schematic_goal ap_comp [comps]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B" "x: A"
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

schematic_goal ap_funcomp_derivation:
  assumes
    "A: U i" "B: U i" "C: U i"
    "f: A \<rightarrow> B" "g: B \<rightarrow> C"
    "x: A" "y: A" "z: A"
    "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: ((g \<circ> f)[p]) = (g[f[p]])"
  apply (equality \<open>p:_\<close>)
    apply (subst funcomp_apply_comp[symmetric], known)+
      apply typechk
    unfolding funcomp_def
    apply (reduce, intros, typechk)
  done


end
