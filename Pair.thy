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


section \<open>Some more results\<close>

lemma* Sig_dist_expand_derivation:
  assumes
    "p: \<Sum>x: A. B x \<times> C x"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "\<And>x. x: A \<Longrightarrow> C x: U i"
  shows "?prf: (\<Sum>x: A. B x) \<times> (\<Sum>x: A. C x)"
  apply (rule SigE[of p])
    focus vars x y
      apply intro
        \<guillemotright> apply intro
            apply assumption
            apply (rule PiE[where ?a=y]; rule fst)
          done
        \<guillemotright> apply intro
            apply assumption
            apply (rule PiE[where ?a=y]; rule snd)
          done
    done
  done

definition "Sig_dist_expand A B C p \<equiv>
  SigInd A (\<lambda>x. B x \<times> C x) (\<lambda>_. (\<Sum>x: A. B x) \<times> (\<Sum>x: A. C x)) (\<lambda>x y. <<x,
  Spartan.fst (B x) (\<lambda>_. C x) `y>, <x, Spartan.snd (B x) (\<lambda>_. C x) `y>>) p"

lemmas Sig_dist_expand [typechk] =
  Sig_dist_expand_derivation [folded Sig_dist_expand_def]


end
