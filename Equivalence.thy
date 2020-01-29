theory Equivalence
imports Identity

begin

definition "homotopic A B f g \<equiv> \<Prod>x: A. f `x =\<^bsub>B x\<^esub> g `x"

definition homotopic_i (infix "~" 100)
  where [implicit]: "f ~ g \<equiv> homotopic ? ? f g"

translations "f ~ g" \<leftharpoondown> "CONST homotopic A B f g"

schematic_goal homotopic_refl_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
  shows "?prf: f ~ f"
  unfolding homotopic_def by intros+ typechk+

schematic_goal homotopic_symmetric_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
  shows "?prf: f ~ g \<rightarrow> g ~ f"
  apply intros
  unfolding homotopic_def
    schematic_subgoal for f
      apply intros
        apply (rule Id_symmetric) defer
          apply typechk+
          schematic_subgoal for x
            apply (rule PiE[of f _ _ x])
          done
          apply typechk+
    done
    apply typechk
  done

schematic_goal homotopic_transitive_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
    "h: \<Prod>x: A. B x"
  shows "?prf: f ~ g \<rightarrow> g ~ h \<rightarrow> f ~ h"
oops


end
