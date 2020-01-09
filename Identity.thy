chapter \<open>The identity type\<close>

text \<open>More about the identity type; the higher groupoid structure of types.\<close>

theory Identity
imports Spartan

begin

(*TODO: Better integration of equality type directly into reasoning...*)

named_theorems eqs \<comment>\<open>For propositional equalities\<close>

thm Id_transitive

schematic_goal pathcomp_left_refl [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x x y (refl x) p =\<^bsub>x=\<^bsub>A\<^esub> y\<^esub> p"
  apply (equality \<open>p: _\<close>)
  apply (rule Id_transitive)
  apply intros
  apply reduce
  done

schematic_goal pathcomp_right_refl [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x y y p (refl y) =\<^bsub>x=\<^bsub>A\<^esub> y\<^esub> p"
  apply (equality \<open>p: _\<close>)
  apply (rule Id_transitive)
  apply intros
  apply reduce
  done

schematic_goal pathcomp_left_inv [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: y =\<^bsub>A\<^esub> x"
  shows "?prf: pathcomp A x y x (pathinv A y x p) p =\<^bsub>x =\<^bsub>A\<^esub> x\<^esub> (refl x)"
  apply (equality \<open>p: _\<close>)
  apply (rule Id_transitive)
  apply (rule Id_symmetric)
  apply reduce
  done

schematic_goal pathcomp_right_inv [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x y x p (pathinv A x y p) =\<^bsub>x =\<^bsub>A\<^esub> x\<^esub> (refl x)"
  apply (equality \<open>p: _\<close>)
    apply (rule Id_transitive)
      apply (rule Id_symmetric)
    apply reduce
  done

schematic_goal pathinv_pathinv [eqs]:
  assumes "A: U i" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathinv A y x (pathinv A x y p) =\<^bsub>x =\<^bsub>A\<^esub> y\<^esub> p"
  by (equality \<open>p: _\<close>) (((rule Id_symmetric)+; routine), (reduce+; routine))

text \<open>
  Associativity of path composition can be proved by a triply-nested path
  induction, which we do here. It can also be proved using functoriality of
  functions, which we'll do later.

  The following proof contains many examples of things that can be improved with
  better setup/automation.
\<close>

schematic_goal pathcomp_assoc:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z" "r: z =\<^bsub>A\<^esub> w"
    "A: U i" "x: A" "y: A" "z: A" "w: A"
  shows "?prf:
    pathcomp A x y w p (pathcomp A y z w q r) =\<^bsub>x =\<^bsub>A\<^esub> w\<^esub>
      pathcomp A x z w (pathcomp A x y z p q) r"
  apply (equality \<open>p: _\<close>)
    apply ((rule Id_transitive)+) [2]
    schematic_subgoal premises for x q
      apply (equality \<open>q: _\<close>)
        apply ((rule Id_transitive; routine?)+) [2]
        schematic_subgoal premises for x r
          apply (equality \<open>r: _\<close>)
            apply ((rule Id_transitive; routine?)+) [2]
            apply reduce
        done
    done
  done

schematic_goal Id_transfer_derivation:
  assumes
    "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
    "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows "?prf: f `x =\<^bsub>B\<^esub> f `y"
  by (equality \<open>p: _\<close>) routine

definition "ap f A B x y p \<equiv> IdInd A (\<lambda>x y _. f `x =\<^bsub>B\<^esub> f `y) (\<lambda>x. refl (f `x)) x y p"

lemma Id_transfer:
  assumes
    "p: x =\<^bsub>A\<^esub> y" "x: A" "y: A"
    "f: A \<rightarrow> B" "A: U i" "B: U i"
  shows "ap f A B x y p: f `x =\<^bsub>B\<^esub> f `y"
  unfolding ap_def by (rule Id_transfer_derivation)

lemma ap_comp [comps]:
  assumes "f: A \<rightarrow> B" "A: U i" "B: U i" "x: A"
  shows "ap f A B x x (refl x) \<equiv> refl (f `x)"
  unfolding ap_def by reduce

(*Okay look, this is very ugly and inconvenient.*)
schematic_goal ap_pathcomp_derivation:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
    "x: A" "y: A" "z: A"
    "p: x =\<^bsub>A\<^esub> y" "q: y =\<^bsub>A\<^esub> z"
  shows
    (*What we want to write: "ap f (p \<bullet> q) = (ap f p) \<bullet> (ap f q)"*)
    "?prf: ap f A B x z (pathcomp A x y z p q) =\<^bsub>(f `x) =\<^bsub>B\<^esub> (f `z)\<^esub>
      pathcomp B (f `x) (f` y) (f `z) (ap f A B x y p) (ap f A B y z q)"
  apply (equality \<open>p: _\<close>)
    apply routine
oops


end
