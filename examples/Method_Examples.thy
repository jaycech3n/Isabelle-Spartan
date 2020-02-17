theory Method_Examples
imports "../Equivalence"

begin

text \<open>
  The \<open>rule\<close> method handles both Pure propositions and propositions-as-types.
\<close>

lemma* rule:
  assumes asm: "\<And>x y. x: A \<Longrightarrow> y: B x \<Longrightarrow> f x y: C x y"
  shows "\<^undefined>: C a b"
  apply (rule asm)
  oops

lemma* rule':
  assumes asm: "f: \<Prod>x: A. \<Prod>y: B x. C x y"
  shows "\<^undefined>: C a b"
  apply (rule asm)
  oops


end
