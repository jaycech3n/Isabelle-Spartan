theory Identity
imports Spartan

begin

(* TODO: Better integration of equality type directly into reasoning? *)

named_theorems eqs \<comment>\<open>For propositional equalities\<close>

method eqs = rule eqs

schematic_goal pathcomp_left_refl [eqs]:
  assumes "A: U" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x x y (refl x) p =\<^bsub>x=\<^bsub>A\<^esub> y\<^esub> p"
apply (rule IdE[of p A x y]; easy?)
  apply (forms; (easy | routine)+)
  apply (reduce; easy?)
    apply (intros+; easy)
done

schematic_goal pathcomp_right_refl [eqs]:
  assumes "A: U" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x y y p (refl y) =\<^bsub>x=\<^bsub>A\<^esub> y\<^esub> p"
apply (rule IdE[of p A x y]; easy?)
  apply (forms; (easy | routine)+)
  apply (reduce; easy?)
    apply (intros+; easy)
done

schematic_goal pathcomp_left_inv [eqs]:
  assumes "A: U" "x: A" "y: A" "p: y =\<^bsub>A\<^esub> x"
  shows "?prf: pathcomp A x y x (pathinv A y x p) p =\<^bsub>x =\<^bsub>A\<^esub> x\<^esub> (refl x)"
apply (rule IdE[of p A y x]; easy?)
  apply (forms; ((easy | routine)+))
  apply (reduce; easy?)+
    apply (intros+; easy)
done

schematic_goal pathcomp_right_inv:
  assumes "A: U" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathcomp A x y x p (pathinv A x y p) =\<^bsub>x =\<^bsub>A\<^esub> x\<^esub> (refl x)"
apply (rule IdE[of p A x y]; easy?)
  apply (forms; ((easy | routine)+))
  apply (reduce; easy?)+
    apply (intros+; easy)
done

schematic_goal inv_of_inv [eqs]:
  assumes "A: U" "x: A" "y: A" "p: x =\<^bsub>A\<^esub> y"
  shows "?prf: pathinv A y x (pathinv A x y p) =\<^bsub>x =\<^bsub>A\<^esub> y\<^esub> p"
apply (rule IdE[of p A x y]; easy?)
  apply (forms; ((easy | routine)+))
  apply (reduce; easy?)+
    apply (intros+; easy)
done

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
apply (rule IdE3[of p A x y q z r w]; known?)
  apply ((routine; easy?); ((intros; easy?); (intros; easy?))+)

  schematic_subgoal premises for x z w q r
    apply (rule IdE2[of q A x z r w]; known?)
      apply ((routine; easy?); ((intros; easy?); (intros; easy?))+)

    schematic_subgoal premises for x z q
      apply (rule IdE[of q A x z]; known?)
        apply ((routine; easy?); ((intros; easy?); (intros; easy?))+)
        apply ((reduce | intros); easy?)+
    done
  done
done


end
