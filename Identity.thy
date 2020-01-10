chapter \<open>The identity type\<close>

text \<open>More about the identity type; the higher groupoid structure of types.\<close>

theory Identity
imports Spartan

begin

(*TODO: Better integration of equality type directly into reasoning...*)

named_theorems eqs \<comment>\<open>For propositional equalities\<close>

schematic_goal pathcomp_left_refl [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x x y (refl x) p =\<^bsub>x=\<^bsub>A\<^esub> y\<^esub> p"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

schematic_goal pathcomp_right_refl [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x y y p (refl y) =\<^bsub>x=\<^bsub>A\<^esub> y\<^esub> p"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

schematic_goal pathcomp_left_inv [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: y =\<^bsub>A\<^esub> x"
  shows "?prf: pathcomp A x y x (pathinv A y x p) p =\<^bsub>x =\<^bsub>A\<^esub> x\<^esub> (refl x)"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

schematic_goal pathcomp_right_inv [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x y x p (pathinv A x y p) =\<^bsub>x =\<^bsub>A\<^esub> x\<^esub> (refl x)"
  apply (equality \<open>p: _\<close>)
    apply (reduce; intros+)
  done

schematic_goal pathinv_pathinv [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathinv A y x (pathinv A x y p) =\<^bsub>x =\<^bsub>A\<^esub> y\<^esub> p"
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
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z" "r: z =\<^bsub>A\<^esub> w"
    "A: U i" "x: A" "y: A" "z: A" "w: A"
  shows "?prf:
    pathcomp A x y w p (pathcomp A y z w q r) =\<^bsub>x =\<^bsub>A\<^esub> w\<^esub>
      pathcomp A x z w (pathcomp A x y z p q) r"
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
    "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
    "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows "?prf: f `x =\<^bsub>B\<^esub> f `y"
  apply (equality \<open>p: _\<close>)
    apply (intros; elims)
  done

definition "ap f A B x y p \<equiv> IdInd A (\<lambda>x y _. f `x =\<^bsub>B\<^esub> f `y) (\<lambda>x. refl (f `x)) x y p"

lemma Id_transfer [typechk]:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "x: A" "y: A"
    "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows "ap f A B x y p: f `x =\<^bsub>B\<^esub> f `y"
  unfolding ap_def by typechk

lemma ap_comp [comps]:
  assumes "f: A \<rightarrow> B" "A: U i" "B: U i" "x: A"
  shows "ap f A B x x (refl x) \<equiv> refl (f `x)"
  unfolding ap_def by reduce

schematic_goal ap_pathcomp_derivation:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A" "z: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows
    \<comment>\<open>
      Okay look, this is ugly and inconvenient. What we want to write instead is
      \<open>ap f (p \<bullet> q) = (ap f p) \<bullet> (ap f q)\<close>
    \<close>
    "?prf: ap f A B x z (pathcomp A x y z p q) =\<^bsub>(f `x) =\<^bsub>B\<^esub> (f `z)\<^esub>
      pathcomp B (f `x) (f` y) (f `z) (ap f A B x y p) (ap f A B y z q)"
  apply (equality \<open>p:_\<close>)
    schematic_subgoal premises for x q
      apply (equality \<open>q:_\<close>)
        apply reduce
          apply intros+
            apply elims
    done
  done


end
