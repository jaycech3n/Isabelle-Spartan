theory Equivalence
imports Identity

begin

definition "homotopy A B f g \<equiv> \<Prod>x: A. f `x =\<^bsub>B x\<^esub> g `x"

definition homotopy_i (infix "~" 100)
  where [implicit]: "f ~ g \<equiv> homotopy ? ? f g"

translations "f ~ g" \<leftharpoondown> "CONST homotopy A B f g"

schematic_goal homotopy_refl_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
  shows "?prf: f ~ f"
  unfolding homotopy_def by intros+ typechk+

schematic_goal homotopy_symmetric_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
  shows "?prf: f ~ g \<rightarrow> g ~ f"
  apply intros
  unfolding homotopy_def
    schematic_subgoal for H
      apply intros
        apply (rule Id_symmetric) defer
          apply typechk+
          schematic_subgoal for x
            apply (rule PiE[of H _ _ x])
          done
          apply typechk+
    done
    apply typechk
  done

schematic_goal homotopy_transitive_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
    "h: \<Prod>x: A. B x"
  shows "?prf: f ~ g \<rightarrow> g ~ h \<rightarrow> f ~ h"
  apply intros+
  unfolding homotopy_def
    schematic_subgoal for H1 H2
      apply intros
        schematic_subgoal for x
          apply (rule Id_transitive[where ?y = "g `x"])
          prefer 5 apply (rule PiE[of H1 _ _ x])
          prefer 5 apply (rule PiE[of H2 _ _ x])
          defer apply typechk+
        done
        apply typechk
    done
    apply typechk+
  done

schematic_goal commute_homotopy_derivation:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
    "f: A \<rightarrow> B" "g: A \<rightarrow> B"
    "H: homotopy A (\<lambda>_. B) f g"
  shows "?prf: (H x) \<bullet> g[p] = f[p] \<bullet> (H y)"
  \<comment>\<open>Need the unfolded version for typechecking:\<close>
  supply assms(8)[unfolded homotopy_def]
  apply (equality \<open>p:_\<close>)
    schematic_subgoal premises for x
      apply reduce
        \<comment>\<open>Here it would really be nice to have automation for transport and
          propositional equality.\<close>
        apply (rule use_transport[where ?x="H x \<bullet> refl (g x)"])
          \<guillemotright> apply (rule pathcomp_right_refl; typechk) done
          \<guillemotright> apply (rule Id_symmetric; typechk?)
              apply (rule pathcomp_left_refl; typechk)
            done
          apply typechk+
    done
  done

no_translations
  "x = y" \<leftharpoondown> "x =\<^bsub>A\<^esub> y"
  "g \<circ> f" \<leftharpoondown> "g \<circ>\<^bsub>A\<^esub> f"
  "p\<inverse>" \<leftharpoondown> "CONST pathinv A x y p"
  "p \<bullet> q" \<leftharpoondown> "CONST pathcomp A x y z p q"
  "fst" \<leftharpoondown> "CONST Spartan.fst A B"
  "snd" \<leftharpoondown> "CONST Spartan.snd A B"
  "f[p]" \<leftharpoondown> "CONST ap A B x y f p"
  "trans P p" \<leftharpoondown> "CONST transport A P x y p"
  "trans_const B p" \<leftharpoondown> "CONST transport_const A B x y p"
  "lift P p u" \<leftharpoondown> "CONST pathlift A P x y p u"
  "apd f p" \<leftharpoondown> "CONST Identity.apd A P f x y p"
  "f ~ g" \<leftharpoondown> "CONST homotopy A B f g"

schematic_goal commute_homotopy'_derivation:
  assumes
    "A: U i"
    "x: A"
    "f: A \<rightarrow> A"
    "H: homotopy A (\<lambda>_. A) f (id A)"
  shows "?prf: H (f x) = f [H x]"
oops


end
