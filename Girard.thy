theory Girard
imports Lambda

begin

text \<open>Experiments in obtaining Girard-type paradoxes. I *want* these to fail!\<close>

abbreviation bot ("\<bottom>") where "\<bottom> \<equiv> \<Prod>A: U. A"
abbreviation not ("\<not>") where "\<not>A \<equiv> A \<rightarrow> \<bottom>"

experiment begin

text \<open>From \<open>A Simplification of Girard's Paradox\<close> (Hurkens, 1995)\<close>

definition
  "\<P> S \<equiv> S \<rightarrow> U"

definition
  "\<U> \<equiv> \<Prod>\<chi>: U. (\<P>(\<P> \<chi>) \<rightarrow> \<chi>) \<rightarrow> \<P>(\<P> \<chi>)"

definition
  "\<tau> t \<equiv> \<lambda>\<chi>: U. \<lambda>f: \<P>(\<P> \<chi>) \<rightarrow> \<chi>. \<lambda>p: \<P> \<chi>. t `(\<lambda>x: \<U>. p `(f `((x `\<chi>) `f)))"

definition
  "\<sigma> s \<equiv> (s `\<U>) `(\<lambda>t: \<P>(\<P> \<U>). \<tau> t)"

term "\<sigma> s"

definition
  "\<Delta> \<equiv> \<lambda>y: \<U>. \<not>(\<Prod>p: \<P> \<U>. \<sigma> y `p \<rightarrow> p `(\<tau> (\<sigma> y)))"

text \<open>This definition fails: type clash for \<open>p\<close>.\<close>

definition
  "\<Omega> \<equiv> \<tau> (\<lambda>p: \<P> \<U>. \<Prod>x: \<U>. (\<sigma> x `p \<rightarrow> p `x))"

end

experiment begin



end


end
