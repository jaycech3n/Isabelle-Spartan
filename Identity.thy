chapter \<open>The identity type\<close>

text \<open>More about the identity type; the higher groupoid structure of types.\<close>

theory Identity
imports Spartan

begin

(* TODO: Better integration of equality type directly into reasoning... *)

named_theorems eqs \<comment>\<open>For propositional equalities\<close>

method eqs = rule eqs

schematic_goal pathcomp_left_refl [eqs]:
  assumes "A: U" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x x y (refl x) p =\<^bsub>x=\<^bsub>A\<^esub> y\<^esub> p"
  by (equality \<open>p: _\<close>) ((rule Id_transitive; routine), (reduce; routine))

schematic_goal pathcomp_right_refl [eqs]:
  assumes "A: U" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x y y p (refl y) =\<^bsub>x=\<^bsub>A\<^esub> y\<^esub> p"
  by (equality \<open>p: _\<close>) ((rule Id_transitive; routine), (reduce; routine))

schematic_goal pathcomp_left_inv [eqs]:
  assumes "A: U" "x: A" "y: A" "p: y =\<^bsub>A\<^esub> x"
  shows "?prf: pathcomp A x y x (pathinv A y x p) p =\<^bsub>x =\<^bsub>A\<^esub> x\<^esub> (refl x)"
  by (equality \<open>p: _\<close>) (((rule Id_transitive Id_symmetric)+; routine?), (reduce+; routine))

schematic_goal pathcomp_right_inv [eqs]:
  assumes "A: U" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x y x p (pathinv A x y p) =\<^bsub>x =\<^bsub>A\<^esub> x\<^esub> (refl x)"
apply (equality \<open>p: _\<close>)
  apply (rule Id_transitive; routine?)
    apply (rule Id_symmetric; routine?)
  apply (reduce+; routine)
done

schematic_goal pathinv_pathinv [eqs]:
  assumes "A: U" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathinv A y x (pathinv A x y p) =\<^bsub>x =\<^bsub>A\<^esub> y\<^esub> p"
  by (equality \<open>p: _\<close>) (((rule Id_symmetric)+; routine), (reduce+; routine))

text \<open>
  Associativity of path composition can be proved by a triply-nested path induction, which
  we do here. It can also be proved using functoriality of functions, which we'll do later.

  The following proof contains many examples of things that can be improved with better
  setup/automation.
\<close>

schematic_goal pathcomp_assoc:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z" "r: z =\<^bsub>A\<^esub> w"
    "A: U" "x: A" "y: A" "z: A" "w: A"
  shows "?prf:
    pathcomp A x y w p (pathcomp A y z w q r) =\<^bsub>x =\<^bsub>A\<^esub> w\<^esub>
      pathcomp A x z w (pathcomp A x y z p q) r"
apply (equality \<open>p: _\<close>)
  apply ((rule Id_transitive; routine?)+) [2]
  schematic_subgoal premises for x q
    apply (equality \<open>q: _\<close>)
      apply ((rule Id_transitive; routine?)+) [2]
      schematic_subgoal premises for x r
        apply (equality \<open>r: _\<close>)
          apply ((rule Id_transitive; routine?)+) [2]
          apply (reduce+; routine)
      done
  done
done

schematic_goal Id_transfer_derivation:
  assumes
    "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
    "f: A \<rightarrow> B" "A: U" "B: U"
  shows "?prf: f `x =\<^bsub>B\<^esub> f `y"
  by (equality \<open>p: _\<close>) routine

definition "ap f A B x y p \<equiv> IdInd A (\<lambda>x y _. f `x =\<^bsub>B\<^esub> f `y) (\<lambda>x. refl (f `x)) x y p"

lemma Id_transfer:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "x: A" "y: A"
    "f: A \<rightarrow> B" "A: U" "B: U"
  shows "ap f A B x y p: f `x =\<^bsub>B\<^esub> f `y"
  unfolding ap_def by (rule Id_transfer_derivation assms)+

lemma ap_comp [reds]:
  assumes "f: A \<rightarrow> B" "A: U" "B: U" "x: A"
  shows "ap f A B x x (refl x) \<equiv> refl (f `x)"
  unfolding ap_def by (reduce | routine)+


end
