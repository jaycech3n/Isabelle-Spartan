(*  Title:      tactics.ML
    Author:     Joshua Chen

General tactics for dependent type theory.
*)

(*An assumption tactic that only solves typing goals with rigid terms and
  judgmental equalities without schematic variables*)
fun assumptions_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val concl = Logic.strip_assums_concl goal
  in
    if
      Lib.is_typing concl andalso Lib.is_rigid (Lib.term_of_typing concl)
      orelse not ((exists_subterm is_Var) concl)
    then assume_tac ctxt i
    else no_tac
  end)

(*Solves typing goals with rigid term by resolving with context facts and
  simplifier premises, or arbitrary goals by *non-unifying* assumption*)
fun known_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val concl = Logic.strip_assums_concl goal
  in
    ((if Lib.is_typing concl andalso Lib.is_rigid (Lib.term_of_typing concl)
      then
        let val ths = map fst (Facts.props (Proof_Context.facts_of ctxt))
        in resolve_tac ctxt (ths @ Simplifier.prems_of ctxt) end
      else K no_tac)
    ORELSE' assumptions_tac ctxt) i
  end)

(*Typechecking: try to solve goals of the form "a: A" where a is rigid*)
fun typechk_tac ctxt =
  let
    val tac = SUBGOAL (fn (goal, i) =>
      if Lib.rigid_typing_concl goal
      then
        let val net = Tactic.build_net
          ((Named_Theorems.get ctxt \<^named_theorems>\<open>typechk\<close>)
          @(Named_Theorems.get ctxt \<^named_theorems>\<open>intros\<close>)
          @(Named_Theorems.get ctxt \<^named_theorems>\<open>elims\<close>))
        in (resolve_from_net_tac ctxt net) i end
      else no_tac)
  in
    CHANGED o REPEAT o REPEAT_ALL_NEW (known_tac ctxt ORELSE' tac)
  end

(*Many methods try to automatically discharge side conditions by typechecking.
  Switch this flag off to discharge by non-unifying assumption instead.*)
val auto_typechk = Attrib.setup_config_bool \<^binding>\<open>auto_typechk\<close> (K true)

(*Combinator runs tactic and tries to discharge all new typing side conditions*)
fun SIDE_CONDS tac ctxt =
  let
    val side_cond_tac =
      if Config.get ctxt auto_typechk then typechk_tac ctxt else known_tac ctxt
  in
    tac THEN_ALL_NEW (TRY o side_cond_tac)
  end

(*Resolves with given rules, discharging as many side conditions as possible*)
fun rule_tac ths ctxt =
  let
    fun mk_rules ths [] = ths
      | mk_rules ths ths' =
          let val ths'' = foldr1 (op @)
            (map (fn th => [th RS @{thm PiE}] handle THM _ => []) ths')
          in
            mk_rules (ths @ ths') ths''
          end
  in
    SIDE_CONDS (resolve_tac ctxt (mk_rules [] ths)) ctxt
  end

(*Applies some introduction rule*)
fun intro_tac ctxt = SUBGOAL (fn (_, i) => SIDE_CONDS
  (resolve_tac ctxt (Named_Theorems.get ctxt \<^named_theorems>\<open>intros\<close>)) ctxt i)

fun intros_tac ctxt = SUBGOAL (fn (_, i) =>
  (CHANGED o REPEAT o CHANGED o intro_tac ctxt) i)

(*Applies an elimination rule and solves the first resulting subgoal,
  which must be a typing judgment for the term being eliminated*)
fun elims_tac ctxt = SUBGOAL (fn (_, i) => SIDE_CONDS
  (resolve_tac ctxt (Named_Theorems.get ctxt \<^named_theorems>\<open>elims\<close>)
    THEN' known_tac ctxt) ctxt i)
