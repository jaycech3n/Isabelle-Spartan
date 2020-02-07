theory Equivalence
imports Identity

begin

section \<open>Homotopy\<close>

definition "homotopy A B f g \<equiv> \<Prod>x: A. f `x =\<^bsub>B x\<^esub> g `x"

definition homotopy_i (infix "~" 100)
  where [implicit]: "f ~ g \<equiv> homotopy ? ? f g"

translations "f ~ g" \<leftharpoondown> "CONST homotopy A B f g"

lemma homotopy_type [typechk]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
  shows "homotopy A B f g: U i"
  unfolding homotopy_def by typechk           

schematic_goal homotopy_refl_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
  shows "?prf: f ~ f"
  unfolding homotopy_def by intros

definition "homotopy_refl A B f \<equiv> \<lambda>x: A. refl (f `x)"

schematic_goal homotopy_refl [typechk]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
  shows "homotopy_refl A B f: f ~ f"
  unfolding homotopy_refl_def homotopy_def by typechk

schematic_goal homotopy_symmetric_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
  shows "?prf: f ~ g \<rightarrow> g ~ f"
  apply intro
  unfolding homotopy_def
    \<guillemotright> for H
      apply intros
        apply (rule Id_symmetric)
          schematic_subgoal for x
            apply (rule PiE[of H _ _ x])
          done
          apply typechk
      done
  done

definition "homotopy_symmetric A B f g \<equiv>
  \<lambda>H: homotopy A (\<lambda>x. B x) f g. \<lambda>x: A. pathinv (B x) (f `x) (g `x) (H `x)"

schematic_goal homotopy_symmetric [typechk]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
  shows "homotopy_symmetric A B f g: f ~ g \<rightarrow> g ~ f"
  unfolding homotopy_symmetric_def homotopy_def by typechk

schematic_goal homotopy_transitive_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
    "h: \<Prod>x: A. B x"
  shows "?prf: f ~ g \<rightarrow> g ~ h \<rightarrow> f ~ h"
  apply intros
  unfolding homotopy_def
    \<guillemotright> for H1 H2
      apply intros
        \<guillemotright> for x
          apply (rule Id_transitive[where ?y = "g `x"])
            apply (rule PiE[of H1 _ _ x])
            apply (rule PiE[of H2 _ _ x])
          done
        \<guillemotright> by typechk
      done
  done

definition "homotopy_transitive A B f g h \<equiv>
  \<lambda>H1: homotopy A (\<lambda>x. B x) f g.
   \<lambda>H2: homotopy A (\<lambda>x. B x) g h.
    \<lambda>x: A. pathcomp (B x) (f `x) (g `x) (h `x) (H1 `x) (H2 `x)"

schematic_goal homotopy_transitive [typechk]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
    "h: \<Prod>x: A. B x"
  shows "homotopy_transitive A B f g h: f ~ g \<rightarrow> g ~ h \<rightarrow> f ~ h"
  unfolding homotopy_transitive_def homotopy_def by typechk

schematic_goal commute_homotopy_derivation:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
    "f: A \<rightarrow> B" "g: A \<rightarrow> B"
    "H: homotopy A (\<lambda>_. B) f g"
  shows "?prf: (H x) \<bullet> g[p] = f[p] \<bullet> (H y)"
  \<comment> \<open>Need this assumption unfolded for typechecking:\<close>
  supply assms(8)[unfolded homotopy_def]
  apply (equality \<open>p:_\<close>)
    schematic_subgoal premises for x
      apply reduce
        \<comment> \<open>Here it would really be nice to have automation for transport and
          propositional equality.\<close>
        apply (rule use_transport[where ?x="H x \<bullet> refl (g x)"])
          apply (rule pathcomp_right_refl)
          apply (rule Id_symmetric[OF _ _ _ pathcomp_left_refl])
    done
  done

schematic_goal commute_homotopy'_derivation:
  assumes
    "A: U i"
    "x: A"
    "f: A \<rightarrow> A"
    "H: homotopy A (\<lambda>_. A) f (id A)"
  shows "?prf: H (f x) = f [H x]"
oops

schematic_goal homotopy_id_left [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "homotopy_refl A B f: (id B) \<circ> f ~ f"
  unfolding homotopy_refl_def homotopy_def by (subst comps) typechk

schematic_goal homotopy_id_right [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "homotopy_refl A B f: f \<circ> (id A) ~ f"
  unfolding homotopy_refl_def homotopy_def by (subst comps) typechk


section \<open>Quasi-inverse\<close>

definition "qinv A B f \<equiv> \<Sum>g: B \<rightarrow> A.
  homotopy A (\<lambda>_. A) (g \<circ>\<^bsub>A\<^esub> f) (id A) \<times> homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> g) (id B)"

lemma qinv_type [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "qinv A B f: U i"
  unfolding qinv_def by typechk

definition qinv_i ("qinv")
  where [implicit]: "qinv f \<equiv> Equivalence.qinv ? ? f"

translations "qinv f" \<leftharpoondown> "CONST Equivalence.qinv A B f"

schematic_goal qinv_id_derivation:
  assumes "A: U i"
  shows "?prf: qinv (id A)"
  unfolding qinv_def
  apply intro defer
    apply intro defer
      apply (rule homotopy_id_right)
      apply (rule homotopy_id_left)
  done

definition "qinv_id A \<equiv>
  <id A, <homotopy_refl A A (id A), homotopy_refl A A (id A)>>"

schematic_goal qinv_id [typechk]:
  assumes "A: U i"
  shows "qinv_id A: qinv (id A)"
  unfolding qinv_id_def qinv_def by typechk


section \<open>Equivalence\<close>

text \<open>
  Following the HoTT book, we first define equivalence in terms of
  bi-invertibility.
\<close>

definition "biinv A B f \<equiv>
  (\<Sum>g: B \<rightarrow> A. homotopy A (\<lambda>_. A) (g \<circ>\<^bsub>A\<^esub> f) (id A))
  \<times> (\<Sum>g: B \<rightarrow> A. homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> g) (id B))"

lemma biinv_type [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "biinv A B f: U i"
  unfolding biinv_def by typechk

definition biinv_i ("biinv")
  where [implicit]: "biinv f \<equiv> Equivalence.biinv ? ? f"

translations "biinv f" \<leftharpoondown> "CONST Equivalence.biinv A B f"

schematic_goal qinv_imp_biinv_derivation:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
  shows "?prf: qinv f \<rightarrow> biinv f"
  apply intros
  unfolding qinv_def biinv_def
    apply (erule Sig_dist_expand; typechk)
  done

definition "qinv_imp_biinv A B f \<equiv>
  \<lambda>x: Equivalence.qinv A B f.
    Sig_dist_expand (B \<rightarrow> A)
      (\<lambda>x. homotopy A (\<lambda>_. A) (x \<circ>\<^bsub>A\<^esub> f) (id A))
      (\<lambda>x. homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> x) (id B)) x"

schematic_goal qinv_imp_biinv [typechk]:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
  shows "qinv_imp_biinv A B f: qinv f \<rightarrow> biinv f"
  unfolding qinv_imp_biinv_def qinv_def biinv_def by typechk

definition equivalence (infix "\<simeq>" 110)
  where "A \<simeq> B \<equiv> \<Sum>f: A \<rightarrow> B. Equivalence.biinv A B f"

lemma [typechk]:
  assumes "A: U i" "B: U i"
  shows "A \<simeq> B: U i"
  unfolding equivalence_def by typechk

schematic_goal equivalence_refl_derivation:
  assumes "A: U i"
  shows "?prf: A \<simeq> A"
  unfolding equivalence_def
  apply intro defer
    \<comment> \<open>
      TODO: would like to just be able to write "rule qinv_imp_biinv" here. The
      following is just tedious.
    \<close>
    apply (rule mp[of "qinv (id A)"]) defer
      apply (rule qinv_id)
      apply (rule qinv_imp_biinv)
  done

definition "equivalence_refl A \<equiv> <id A, qinv_imp_biinv A A (id A) `qinv_id A>"

lemma equivalence_refl [typechk]:
  "A: U i \<Longrightarrow> equivalence_refl A: A \<simeq> A"
  unfolding equivalence_refl_def equivalence_def by typechk

declare [[quick_and_dirty]]

schematic_goal equivalence_symmetric_derivation:
  assumes "A: U i" "B: U i"
  shows "?prf: A \<simeq> B \<rightarrow> B \<simeq> A"
  apply intros
  unfolding equivalence_def
    \<guillemotright> for p
      \<comment> \<open>
        The following is very low-level; we'd like to just eliminate and get
          \<open>f \<equiv> fst p: A \<rightarrow> B\<close> and \<open>hyp \<equiv> snd p: biinv A B f\<close>
        usable in the context.
      \<close>
      apply (erule elims)
        apply typechk
      sorry
  done

text \<open>
  Equal types are equivalent. Again we follow the HoTT book and show that
  transport is an equivalence, instead of using equality induction.

  The following proof is a bit wordy because (1) the typechecker doesn't
  rewrite, and (2) we don't yet have universe automation.
\<close>

schematic_goal id_imp_equiv_derivation:
  assumes
    "A: U i" "B: U i" "p: A =\<^bsub>U i\<^esub> B"
  shows "<trans (id (U i)) p, ?isequiv>: A \<simeq> B"
  unfolding equivalence_def
  apply intros defer
    \<guillemotright> apply (equality \<open>p:_\<close>)
      \<guillemotright> premises for A B

        \<comment> \<open>Switch off auto-typechecking, which messes with universe levels\<close>
        supply [[auto_typechk=false, greedy_typechk=false]]
        
        apply (subst id_comp[symmetric, of A], typechk)
          apply (subst id_comp[symmetric, of B], typechk)
            apply (rule transport)
              apply (rule U_in_U, typechk)
              supply [[auto_typechk, greedy_typechk]]
              apply (rule lift_universe_codomain; rule U_in_U)
        done
      \<guillemotright> premises for A
        apply (subst transport_comp)
          apply typechk
          apply (rule U_in_U, rule lift_universe)
          apply (rule U_in_U)
          apply reduce
            apply (rule mp[of "qinv (id A)"])
              apply (rule qinv_id)
              apply (rule qinv_imp_biinv)
        done
      done
    \<guillemotright> \<comment> \<open>Same proof as in the first subgoal above\<close>
      supply [[auto_typechk=false, greedy_typechk=false]]
      apply (subst (2) id_comp[symmetric, of A], typechk)
        apply (subst (2) id_comp[symmetric, of B], typechk)
          apply (rule transport)
            apply (rule U_in_U, typechk)
            supply [[auto_typechk, greedy_typechk]]
            apply (rule lift_universe_codomain; rule U_in_U)
      done
  done


end
