theory Implicit_Args
imports Spartan

begin

consts
  imp_arg   :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> 'a\<close>
  imp_dummy :: \<open>'a\<close> ("?")

syntax
  "_imp_arg" :: \<open>id_position \<Rightarrow> logic\<close> ("{_}")
translations
  "{x}" \<rightleftharpoons> "CONST imp_arg (\<lambda>x. ?)"

definition imp_annotation :: \<open>'a \<Rightarrow> 'a Type \<Rightarrow> 'a\<close> (infix ":>" 5)
  where "x :> _ \<equiv> x"

ML_file \<open>implicit_args.ML\<close>

ML \<open>
fun probe (n: int) _ ts =
  let
    fun pretty_list xs =
      space_implode "\n" (map (fn x => "\<^item> " ^  @{make_string} x) xs)

    val _ = tracing (
      "Syntax phase level " ^ @{make_string} n ^ "\n\nTerms\n-----\n" ^
      (space_implode "\n" (map (fn t => "\<^item> " ^  @{make_string} t) ts)) ^
      "\n\nAnnotations\n-----------\n" ^
      pretty_list (map Implicit_Args.annotations_of ts)
    )
  in
    ts
  end

val _ = Context.>>
  (Syntax_Phases.term_check ~5 "" (probe ~5)
  #> Syntax_Phases.term_check 0 "" (probe 0)
  #> Syntax_Phases.term_check 1 "" (probe 1))
\<close>


section \<open>Examples\<close>

text \<open>Want to be able to write, for example:\<close>

abbreviation funcomp_i (infixr "\<circ>" 100)
  where "g \<circ> f \<equiv> funcomp {A} g (f :> {A} \<rightarrow> ?)"

abbreviation Id_i (infix "=" 100)
  where "x = y \<equiv> (x :> {A}) =\<^bsub>{A}\<^esub> (y :> {A})"

abbreviation "pathinv_i p \<equiv> pathinv {A} {x} {y} (p :> {x} =\<^bsub>{A}\<^esub> {y})"

abbreviation (input) "pathcomp_i p q \<equiv>
  pathcomp {A} {x} {y} {z} (p :> {x} =\<^bsub>{A}\<^esub> {y}) (q :> {y} =\<^bsub>{A}\<^esub> {z})"

bundle pathinv_syntax
begin
  notation pathinv_i ("_\<inverse>")
end

bundle no_pathinv_syntax
begin
  no_notation pathinv_i ("_\<inverse>")
end

bundle pathcomp_syntax
begin
  notation pathcomp_i (infixl "\<bullet>" 120)
end

bundle no_pathcomp_syntax
begin
  no_notation pathcomp_i (infixl "\<bullet>" 120)
end

unbundle pathinv_syntax pathcomp_syntax

term "p \<bullet> q"

end
