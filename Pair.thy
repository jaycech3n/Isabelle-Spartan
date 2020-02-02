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

schematic_goal Sig_dist_expand_derivation:
  assumes
    "p: \<Sum>x: A. B x \<times> C x"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "\<And>x. x: A \<Longrightarrow> C x: U i"
  shows "?prf: (\<Sum>x: A. B x) \<times> (\<Sum>x: A. C x)"
  (*This takes more work than it perhaps should...*)
  apply (rule SigE[of p]) prefer 4
    apply intros defer
    \<guillemotright> for x y
      apply intros prefer 3
        apply (rule PiE[where ?a=y])
          apply (rule fst)
          apply typechk+
      done
    \<guillemotright> for x y
      apply intros prefer 3
        apply (rule PiE[where ?a=y])
          apply (rule snd)
          apply typechk+
      done
    apply typechk+
  done

definition "Sig_dist_expand A B C p \<equiv> SigInd A
  (\<lambda>x. B x \<times> C x)
  (\<lambda>_. (\<Sum>x: A. B x) \<times> (\<Sum>x: A. C x))
  (\<lambda>x y.
    < <x, Spartan.fst (B x) (\<lambda>_. C x) `y>,
      <x, Spartan.snd (B x) (\<lambda>_. C x) `y> >)
  p"

lemma Sig_dist_expand [typechk]:
  assumes
    "p: \<Sum>x: A. B x \<times> C x"
    "A: U i"
    "\<And>x. x: A \<Longrightarrow> B x: U i"
    "\<And>x. x: A \<Longrightarrow> C x: U i"
  shows "Sig_dist_expand A B C p: (\<Sum>x: A. B x) \<times> (\<Sum>x: A. C x)"
  unfolding Sig_dist_expand_def by typechk


end