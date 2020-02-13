theory Equivalence
imports Identity

begin

section \<open>Homotopy\<close>

definition "homotopy A B f g \<equiv> \<Prod>x: A. f `x =\<^bsub>B x\<^esub> g `x"

definition homotopy_i (infix "~" 100)
  where [implicit]: "f ~ g \<equiv> homotopy ? ? f g"

translations "f ~ g" \<leftharpoondown> "CONST homotopy A B f g"

lemma* homotopy_type [typechk]:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x" "g: \<Prod>x: A. B x"
  shows "f ~ g: U i"
  unfolding homotopy_def by typechk

lemma* homotopy_refl_derivation:
  assumes
    "A: U i"
    "f: \<Prod>x: A. B x"
  shows "{}: f ~ f"
  unfolding homotopy_def by intros

definition "homotopy_refl A f \<equiv> \<lambda>x: A. refl (f `x)"

lemmas homotopy_refl [typechk] =
  homotopy_refl_derivation [folded homotopy_refl_def]

lemma* homotopy_symmetric_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
  shows "H: f ~ g \<Longrightarrow> {}: g ~ f"
  unfolding homotopy_def
  apply intros
    apply (rule Id_symmetric)
      \<guillemotright> by (rule PiE[of H])
      \<guillemotright> by typechk
  done

definition "homotopy_symmetric A B f g H \<equiv>
  \<lambda>x: A. pathinv (B x) (f `x) (g `x) (H `x)"

lemmas homotopy_symmetric [typechk] =
  homotopy_symmetric_derivation [folded homotopy_symmetric_def]

lemma* homotopy_transitive_derivation:
  assumes
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "f: \<Prod>x: A. B x"
    "g: \<Prod>x: A. B x"
    "h: \<Prod>x: A. B x"
  shows "\<lbrakk>H1: f ~ g; H2: g ~ h\<rbrakk> \<Longrightarrow> {}: f ~ h"
  unfolding homotopy_def
  apply intro
    \<guillemotright> vars x
      apply (rule Id_transitive[where ?y="g x"])
        \<^item> by (rule PiE[of H1])
        \<^item> by (rule PiE[of H2])
      done
    \<guillemotright> by typechk
  done

definition "homotopy_transitive A B f g h H1 H2 \<equiv>
  \<lambda>x: A. pathcomp (B x) (f `x) (g `x) (h `x) (H1 `x) (H2 `x)"

lemmas homotopy_transitive [typechk] =
  homotopy_transitive_derivation [folded homotopy_transitive_def]

lemma* commute_homotopy_derivation:
  assumes
    "A: U i" "B: U i"
    "x: A" "y: A"
    "p: x =\<^bsub>A\<^esub> y"
    "f: A \<rightarrow> B" "g: A \<rightarrow> B"
    "H: homotopy A (\<lambda>_. B) f g"
  shows "{}: (H x) \<bullet> g[p] = f[p] \<bullet> (H y)"
  \<comment> \<open>Need this assumption unfolded for typechecking:\<close>
  supply assms(8)[unfolded homotopy_def]
  apply (equality \<open>p:_\<close>)
    focus vars x
      apply reduce
        \<comment> \<open>Here it would really be nice to have automation for transport and
          propositional equality.\<close>
        apply (rule use_transport[where ?x="H x \<bullet> refl (g x)"])
          \<guillemotright> by (rule pathcomp_right_refl)
          \<guillemotright> by (rule Id_symmetric) (rule pathcomp_left_refl)
          \<guillemotright> by typechk
    done
  done

corollary* commute_homotopy'_derivation:
  assumes
    "A: U i"
    "x: A"
    "f: A \<rightarrow> A"
    "H: homotopy A (\<lambda>_. A) f (id A)"
  shows "{}: H (f x) = f [H x]"
oops

lemma* homotopy_id_left [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "homotopy_refl A f: (id B) \<circ> f ~ f"
  unfolding homotopy_refl_def homotopy_def by (subst comps) typechk

lemma* homotopy_id_right [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "homotopy_refl A f: f \<circ> (id A) ~ f"
  unfolding homotopy_refl_def homotopy_def by (subst comps) typechk

lemma* homotopy_funcomp_left:
  assumes
    "A: U i" "B: U i"
    "\<And>x. x: B \<Longrightarrow> C x: U i"
    "f: A \<rightarrow> B"
    "g: \<Prod>x: B. C x"
    "g': \<Prod>x: B. C x"
    "H: homotopy B C g g'"
  shows "{}: homotopy A {} (g \<circ>\<^bsub>A\<^esub> f) (g' \<circ>\<^bsub>A\<^esub> f)"
  unfolding homotopy_def
  apply (intro; reduce)
    apply (insert \<open>H: _\<close>[unfolded homotopy_def])
      apply (erule PiE[of H]; typechk)
  done

lemma* homotopy_funcomp_right:
  assumes
    "A: U i" "B: U i" "C: U i"
    "f: A \<rightarrow> B"
    "f': A \<rightarrow> B"
    "g: B \<rightarrow> C"
    "H: homotopy A (\<lambda>_. B) f f'"
  shows "{}: homotopy A {} (g \<circ>\<^bsub>A\<^esub> f) (g \<circ>\<^bsub>A\<^esub> f')"
  unfolding homotopy_def
  apply (intro; reduce)
    apply (insert \<open>H: _\<close>[unfolded homotopy_def]; drule PiE, assumption)
      apply (rule Id_transfer, assumption)
  done


section \<open>Quasi-inverse and bi-invertibility\<close>

subsection \<open>Quasi-inverses\<close>

definition "qinv A B f \<equiv> \<Sum>g: B \<rightarrow> A.
  homotopy A (\<lambda>_. A) (g \<circ>\<^bsub>A\<^esub> f) (id A) \<times> homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> g) (id B)"

lemma qinv_type [typechk]:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "qinv A B f: U i"
  unfolding qinv_def by typechk

definition qinv_i ("qinv")
  where [implicit]: "qinv f \<equiv> Equivalence.qinv ? ? f"

translations "qinv f" \<leftharpoondown> "CONST Equivalence.qinv A B f"

lemma* qinv_id_derivation:
  assumes "A: U i"
  shows "{}: qinv (id A)"
  unfolding qinv_def
  apply intro defer
    apply intro defer
      apply (rule homotopy_id_right)
      apply (rule homotopy_id_left)
  done

definition "qinv_id A \<equiv> <id A, <homotopy_refl A (id A), homotopy_refl A (id A)>>"

lemmas qinv_id [typechk] = qinv_id_derivation [folded qinv_id_def]

lemma* quasiinv_qinv_derivation:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "prf: qinv f \<Longrightarrow> {}: qinv (fst prf)"
  unfolding qinv_def
  apply intro
    \<guillemotright> by (rule \<open>f:_\<close>)
    \<guillemotright> apply (erule SigE, typechk)
        focus vars g HH
          apply intro
            \<^item> by reduce (rule PiE[where ?a=HH]; rule snd)
            \<^item> by reduce (rule PiE[where ?a=HH]; rule fst)
        done
      done
  done

definition "quasiinverse_qinv A B f prf \<equiv>
  <f, SigInd (B \<rightarrow> A) (\<lambda>g. homotopy A (\<lambda>_. A) (g \<circ>\<^bsub>A\<^esub> f) (id A) \<times> homotopy B
  (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> g) (id B)) (\<lambda>a. homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> Spartan.fst (B \<rightarrow> A)
  (\<lambda>x. homotopy A (\<lambda>_. A) (x \<circ>\<^bsub>A\<^esub> f) (id A) \<times> homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> x)
  (id B)) `a) (id B) \<times> homotopy A (\<lambda>_. A) (Spartan.fst (B \<rightarrow> A) (\<lambda>x. homotopy A
  (\<lambda>_. A) (x \<circ>\<^bsub>A\<^esub> f) (id A) \<times> homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> x) (id B)) `a \<circ>\<^bsub>A\<^esub> f)
  (id A)) (\<lambda>g HH. <Spartan.snd (homotopy A (\<lambda>_. A) (g \<circ>\<^bsub>A\<^esub> f) (id A)) (\<lambda>x.
  homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> g) (id B)) `HH, Spartan.fst (homotopy A (\<lambda>_. A)
  (g \<circ>\<^bsub>A\<^esub> f) (id A)) (\<lambda>x. homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> g) (id B)) `HH>) prf>"

lemmas quasiinverse_qinv =
  quasiinv_qinv_derivation [folded quasiinverse_qinv_def]

subsection \<open>Bi-invertible maps\<close>

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

lemma* qinv_imp_biinv_derivation:
  assumes
    "A: U i" "B: U i"
    "f: A \<rightarrow> B"
  shows "{}: qinv f \<rightarrow> biinv f"
  apply intros
  unfolding qinv_def biinv_def
    apply (erule Sig_dist_expand; typechk)
  done

definition "qinv_imp_biinv A B f \<equiv>
  \<lambda>x: Equivalence.qinv A B f. Sig_dist_expand (B \<rightarrow> A) (\<lambda>x. homotopy A (\<lambda>_. A)
  (x \<circ>\<^bsub>A\<^esub> f) (id A)) (\<lambda>x. homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> x) (id B)) x"

lemmas qinv_imp_biinv [typechk] =
  qinv_imp_biinv_derivation [folded qinv_imp_biinv_def]

text \<open>
  Show that bi-invertible maps are quasi-inverses, as a demonstration of how to
  work in this system.
\<close>

lemma* biinv_imp_qinv_derivation:
  assumes "A: U i" "B: U i" "f: A \<rightarrow> B"
  shows "{}: biinv f \<rightarrow> qinv f"

  text \<open>Split the hypothesis \<^term>\<open>biinv f\<close> into its components:\<close>
  apply intro
  unfolding biinv_def
  apply (erule SigE, typechk)+

  text \<open>Name the components:\<close>
  \<guillemotright> premises vars _ _ _ g H1 h H2
  thm \<open>g:_\<close> \<open>h:_\<close> \<open>H1:_\<close> \<open>H2:_\<close>

  text \<open>
    \<^term>\<open>g\<close> is a quasi-inverse to \<^term>\<open>f\<close>, so the proof will be a triple
    \<^term>\<open><g, <?H1, ?H2>>\<close>.
  \<close>
  unfolding qinv_def
  apply intro
    \<guillemotright> by (rule \<open>g: _\<close>)
    \<guillemotright> apply intro
      text \<open>The first part \<^prop>\<open>?H1: g \<circ> f ~ id A\<close> is given by \<^term>\<open>H1\<close>.\<close>
      apply (rule \<open>H1: _\<close>)

      text \<open>
        It remains to prove \<^prop>\<open>?H2: f \<circ> g ~ id B\<close>. First show that \<open>g ~ h\<close>,
        then the result follows from @{thm \<open>H2: f \<circ> h ~ id B\<close>}. Here a proof
        block is used to calculate "forward".
      \<close>
      proof -
        have "?\<alpha>: g ~ g \<circ> f \<circ> h"
          apply (subst id_right[symmetric], typechk)
          apply (rule homotopy_funcomp_right)
          apply (rule homotopy_symmetric)
          text \<open>Now we are done since this is known.\<close>
          by fact

        moreover
        have "?\<beta>: g \<circ> f \<circ> h ~ h"
          apply (subst (2) id_left[symmetric, of h], typechk)
          apply (subst funcomp_assoc[symmetric], typechk)
          apply (rule homotopy_funcomp_left)
          by fact
  
        ultimately
        have "?\<gamma>: g ~ h"
          apply (rule homotopy_transitive) defer
          by assumption+ typechk
  
        then
        have "?\<delta>: f \<circ> g ~ f \<circ> h"
          by (rule homotopy_funcomp_right)
  
        thus "?H2: f \<circ> g ~ id B"
          apply (rule homotopy_transitive) defer
          by (assumption, rule \<open>H2:_\<close>) typechk
      qed
    done
  done

definition "biinv_imp_qinv A B f \<equiv>
  \<lambda>x: Equivalence.biinv A B f. SigInd (\<Sum>g: B \<rightarrow> A. homotopy A (\<lambda>_. A) (g \<circ>\<^bsub>A\<^esub> f)
  (id A)) (\<lambda>_. \<Sum>g: B \<rightarrow> A. homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> g) (id B)) (\<lambda>a.
  Equivalence.qinv A B f) (\<lambda>uua y. SigInd (B \<rightarrow> A) (\<lambda>g. homotopy A (\<lambda>_. A) (g
  \<circ>\<^bsub>A\<^esub> f) (id A)) (\<lambda>a. Equivalence.qinv A B f) (\<lambda>g ya. SigInd (B \<rightarrow> A) (\<lambda>g.
  homotopy B (\<lambda>_. B) (f \<circ>\<^bsub>B\<^esub> g) (id B)) (\<lambda>a. Equivalence.qinv A B f) (\<lambda>h H2. <g,
  <ya, homotopy_transitive B (\<lambda>x. B) (f \<circ>\<^bsub>B\<^esub> g) (f \<circ>\<^bsub>B\<^esub> h) (id B) (\<lambda>x: B. ap A B
  (g `x) (h `x) f (homotopy_transitive B (\<lambda>x. A) g (g \<circ>\<^bsub>B\<^esub> f \<circ>\<^bsub>B\<^esub> h) h (\<lambda>x: B.
  ap B A (id B `x) ((f \<circ>\<^bsub>B\<^esub> h) `x) g (homotopy_symmetric B (\<lambda>x. B) (f \<circ>\<^bsub>B\<^esub> h)
  (id B) H2 `x)) (\<lambda>x: B. ya `(h `x)) `x)) H2>>) y) uua) x"

lemmas biinv_imp_qinv [typechk] =
  biinv_imp_qinv_derivation [folded biinv_imp_qinv_def]

lemma* biinv_id_derivation:
  "A: U i \<Longrightarrow> {}: biinv (id A)"
  by (rule qinv_imp_biinv) (rule qinv_id)

definition "biinv_id A \<equiv> qinv_imp_biinv A A (id A) (qinv_id A)"

lemmas biinv_id [typechk] = biinv_id_derivation [folded biinv_id_def]


section \<open>Equivalence\<close>

text \<open>
  Following the HoTT book, we first define equivalence in terms of
  bi-invertibility.
\<close>

definition equivalence (infix "\<simeq>" 110)
  where "A \<simeq> B \<equiv> \<Sum>f: A \<rightarrow> B. Equivalence.biinv A B f"

lemma equivalence_type [typechk]:
  assumes "A: U i" "B: U i"
  shows "A \<simeq> B: U i"
  unfolding equivalence_def by typechk

lemma* equivalence_refl_derivation:
  assumes "A: U i"
  shows "{}: A \<simeq> A"
  unfolding equivalence_def
  apply intro defer
    apply (rule qinv_imp_biinv) defer
      apply (rule qinv_id)
  done

definition "equivalence_refl A \<equiv> <id A, qinv_imp_biinv A A (id A) `qinv_id A>"

lemmas equivalence_refl [typechk] =
  equivalence_refl_derivation [folded equivalence_refl_def]

text \<open>
  The following could perhaps be easier with transport (but then I think we need
  univalence?)...
\<close>

lemma* equivalence_symmetric_derivation:
  assumes "A: U i" "B: U i"
  shows "{}: A \<simeq> B \<rightarrow> B \<simeq> A"
  apply intros
  unfolding equivalence_def
  apply (erule elims, typechk)
  \<guillemotright> vars _ f "prf"
    (*Definitely getting into the low-level here.*)
    apply (drule biinv_imp_qinv[THEN PiE, rotated 3], typechk)
    apply intro
      \<^item> unfolding qinv_def
        apply (rule fst) defer
        by assumption typechk
      \<^item> by (rule qinv_imp_biinv) (rule quasiinverse_qinv)
    done
  done

text \<open>
  Equal types are equivalent. We give two proofs: the first by induction, and
  the second by following the HoTT book and showing that transport is an
  equivalence.
\<close>

lemma* id_imp_equiv_derivation':
  assumes
    "A: U i" "B: U i" "p: A =\<^bsub>U i\<^esub> B"
  shows "{}: A \<simeq> B"
  by (equality \<open>p:_\<close>) (rule equivalence_refl)

text \<open>
  The following proof is a bit wordy because (1) the typechecker doesn't
  rewrite, and (2) we don't yet have universe automation.
\<close>

lemma* id_imp_equiv_derivation:
  assumes
    "A: U i" "B: U i" "p: A =\<^bsub>U i\<^esub> B"
  shows "<trans (id (U i)) p, ?isequiv>: A \<simeq> B"
  unfolding equivalence_def
  apply intros defer
    \<guillemotright> apply (equality \<open>p:_\<close>)
      \<^item> premises vars A B
        \<comment> \<open>Switch off auto-typechecking, which messes with universe levels\<close>
        supply [[auto_typechk=false]]

        apply (subst id_comp[symmetric, of A]) ~ by typechk
        apply (subst id_comp[symmetric, of B]) ~ by typechk
        apply (rule transport, rule U_in_U, typechk)
        apply (rule lift_universe_codomain, rule U_in_U, typechk)
        apply (rule U_in_U)
        done
      \<^item> premises vars A
        apply (subst transport_comp)
          \<^enum> by typechk
          \<^enum> by (rule U_in_U)
          \<^enum> by (rule lift_universe)
          \<^enum> apply reduce
              apply (rule qinv_imp_biinv)
                apply (rule qinv_id)
            done
        done
      done

    \<guillemotright> \<comment> \<open>Similar proof as in the first subgoal above\<close>
      supply [[auto_typechk=false]]
      apply (subst (2) id_comp[symmetric, of A]) ~ by typechk
      apply (subst (2) id_comp[symmetric, of B]) ~ by typechk
      apply (rule transport, rule U_in_U, typechk)
      apply (rule lift_universe_codomain, rule U_in_U, typechk)
      apply (rule U_in_U)
      done
  done

(*Uncomment this to see all implicits from here on.
no_translations
  "f x" \<leftharpoondown> "f `x"
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
  "qinv f" \<leftharpoondown> "CONST Equivalence.qinv A B f"
  "biinv f" \<leftharpoondown> "CONST Equivalence.biinv A B f"
*)


end
