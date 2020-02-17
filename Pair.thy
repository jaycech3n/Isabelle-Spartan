theory Pair
imports Spartan

begin

section \<open>Notation\<close>

definition fst_i ("fst")
  where [implicit]: "fst \<equiv> Spartan.fst ? ?"

definition snd_i ("snd")
  where [implicit]: "snd \<equiv> Spartan.snd ? ?"

translations
  "fst" \<leftharpoondown> "CONST Spartan.fst A B"
  "snd" \<leftharpoondown> "CONST Spartan.snd A B"


section \<open>Projections\<close>

lemma* fst [typechk]:
  assumes
    "p: \<Sum>x: A. B x"
    "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "fst p: A"
  by typechk

lemma* snd [typechk]:
  assumes
    "p: \<Sum>x: A. B x"
    "A: U i" "\<And>x. x: A \<Longrightarrow> B x: U i"
  shows "snd p: B (fst p)"
  by typechk

method fst for p::o = rule fst[of p]
method snd for p::o = rule snd[of p]


section \<open>Properties of \<Sigma>\<close>

lemma* Sig_dist_expand_derivation:
  assumes
    "p: \<Sum>x: A. B x \<times> C x"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "\<And>x. x: A \<Longrightarrow> C x: U i"
  shows "\<^undefined>: (\<Sum>x: A. B x) \<times> (\<Sum>x: A. C x)"
  apply (elim p)
    focus vars x y
      apply intro
        \<guillemotright> apply intro
            apply assumption
            apply (fst y)
          done
        \<guillemotright> apply intro
            apply assumption
            apply (snd y)
          done
    done
  done

definition "Sig_dist_expand A B C p \<equiv>
  SigInd A (\<lambda>x. B x \<times> C x) (\<lambda>_. (\<Sum>x: A. B x) \<times> (\<Sum>x: A. C x)) (\<lambda>x y. <<x,
  Spartan.fst (B x) (\<lambda>_. C x) `y>, <x, Spartan.snd (B x) (\<lambda>_. C x) `y>>) p"

lemmas Sig_dist_expand [typechk] =
  Sig_dist_expand_derivation [folded Sig_dist_expand_def]


end
