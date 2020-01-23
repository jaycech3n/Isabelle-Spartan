(*  Title:      schematic_subgoal.ML
    Author:     Joshua Chen

A modified version of the Isar `subgoal` command that keeps
schematic variables in the goal state.
*)

local

fun param_bindings ctxt (param_suffix, raw_param_specs) st =
  let
    val _ = if Thm.no_prems st then error "No subgoals!" else ()
    val subgoal = #1 (Logic.dest_implies (Thm.prop_of st))
    val subgoal_params =
      map (apfst (Name.internal o Name.clean)) (Term.strip_all_vars subgoal)
      |> Term.variant_frees subgoal |> map #1

    val n = length subgoal_params
    val m = length raw_param_specs
    val _ =
      m <= n orelse
        error ("Excessive subgoal parameter specification" ^
          Position.here_list (map snd (drop n raw_param_specs)))

    val param_specs =
      raw_param_specs |> map
        (fn (NONE, _) => NONE
          | (SOME x, pos) =>
              let
                val b = #1 (#1 (Proof_Context.cert_var (Binding.make (x, pos), NONE, NoSyn) ctxt))
                val _ = Variable.check_name b
              in SOME b end)
      |> param_suffix ? append (replicate (n - m) NONE)

    fun bindings (SOME x :: xs) (_ :: ys) = x :: bindings xs ys
      | bindings (NONE :: xs) (y :: ys) = Binding.name y :: bindings xs ys
      | bindings _ ys = map Binding.name ys
  in bindings param_specs subgoal_params end

local

fun lift_import idx params th ctxt =
  let
    val ((_, [th']), ctxt') = Variable.importT [th] ctxt;

    val Ts = map Thm.typ_of_cterm params;
    val ts = map Thm.term_of params;

    val prop = Thm.full_prop_of th';
    val concl_vars = Term.add_vars (Logic.strip_imp_concl prop) [];
    val vars = rev (Term.add_vars prop []);
    val (ys, ctxt'') = Variable.variant_fixes (map (Name.clean o #1 o #1) vars) ctxt';

    fun var_inst v y =
      let
        val ((x, i), T) = v;
        val (U, args) =
          if member (op =) concl_vars v then (T, [])
          else (Ts ---> T, ts);
        val u = Free (y, U);
        in ((Var v, list_comb (u, args)), (u, Var ((x, i + idx), U))) end;
    val (inst1, inst2) =
      split_list (map (apply2 (apply2 (Thm.cterm_of ctxt))) (map2 var_inst vars ys));

    val th'' = Thm.instantiate ([], map (apfst (Term.dest_Var o Thm.term_of)) inst1) th';
  in ((inst2, th''), ctxt'') end

fun lift_subgoals ctxt params asms th =
  let
    fun lift ct = fold_rev (Thm.all_name ctxt) params (Drule.list_implies (asms, ct));
    val unlift =
      fold (Thm.elim_implies o Thm.assume) asms o
      Drule.forall_elim_list (map #2 params) o Thm.assume;
    val subgoals = map lift (Drule.strip_imp_prems (Thm.cprop_of th));
    val th' = fold (Thm.elim_implies o unlift) subgoals th;
  in (subgoals, th') end;

fun retrofit ctxt1 ctxt0 params asms i st1 st0 =
  let
    val idx = Thm.maxidx_of st0 + 1;
    val ps = map #2 params;
    val ((subgoal_inst, st2), ctxt2) = lift_import idx ps st1 ctxt1;
    val (subgoals, st3) = lift_subgoals ctxt2 params asms st2;
    val result = st3
      |> Goal.conclude
      |> Drule.implies_intr_list asms
      |> Drule.forall_intr_list ps
      |> Drule.implies_intr_list subgoals
      |> fold_rev (Thm.forall_intr o #1) subgoal_inst
      |> fold (Thm.forall_elim o #2) subgoal_inst
      |> Thm.adjust_maxidx_thm idx
      |> singleton (Variable.export ctxt2 ctxt0)

val _ = tracing (@{make_string} result)
val _ = tracing (@{make_string} (Thm.nprems_of st1))
val _ = tracing (@{make_string} st1)
val _ = tracing (@{make_string} st0)
val _ = tracing (@{make_string}
  (Seq.list_of(Thm.bicompose (SOME ctxt0) {flatten = true, match = false, incremented = false}
      (false, result, Thm.nprems_of st1) i st0)))

  in
    Thm.bicompose (SOME ctxt0) {flatten = true, match = false, incremented = false}
      (false, result, Thm.nprems_of st1) i st0
  end

in

fun gen_schematic_subgoal prep_atts raw_result_binding raw_prems_binding param_specs state =
  let
    val _ = Proof.assert_backward state

    val state1 = state
      |> Proof.map_context (Proof_Context.set_mode Proof_Context.mode_schematic)
      |> Proof.refine_insert []

    val {context = ctxt, facts = facts, goal = st} = Proof.raw_goal state1

    val result_binding = apsnd (map (prep_atts ctxt)) raw_result_binding
    val (prems_binding, do_prems) =
      (case raw_prems_binding of
        SOME (b, raw_atts) => ((b, map (prep_atts ctxt) raw_atts), true)
      | NONE => (Binding.empty_atts, false))

    val (subgoal_focus, _) =
      (if do_prems then Subgoal.focus_prems else Subgoal.focus_params) ctxt
        1 (SOME (param_bindings ctxt param_specs st)) st

    fun after_qed (ctxt'', [[result]]) =
      Proof.end_block #> (fn state' =>
        let
          val ctxt' = Proof.context_of state'
          val results' =
            Proof_Context.export ctxt'' ctxt' (Conjunction.elim_conjunctions result)
        in
          state'
          |> tap (K (@{print} "["))
          |> Proof.refine_primitive (fn _ => fn _ =>
            (* Subgoal. *)retrofit ctxt'' ctxt' (#params subgoal_focus) (#asms subgoal_focus) 1
              (Goal.protect 0 result) st
            |> tap (fn ths => (
              @{print} result;
              @{print} (Seq.list_of ths)))
            |> Seq.hd)
          |> tap (K (@{print} "]"))
          |> Proof.map_context
            (#2 o Proof_Context.note_thmss "" [(result_binding, [(results', [])])])
        end)
      #> Proof.reset_facts
      #> Proof.enter_backward
  in
    state1
    |> Proof.enter_forward
    |> Proof.using_facts []
    |> Proof.begin_block
    |> Proof.map_context (fn _ =>
      #context subgoal_focus
      |> Proof_Context.note_thmss "" [(prems_binding, [(#prems subgoal_focus, [])])] |> #2)
    |> Proof.internal_goal (K (K ())) (Proof_Context.get_mode ctxt) true "subgoal"
        NONE after_qed [] [] [(Binding.empty_atts, [(Thm.term_of (#concl subgoal_focus), [])])] |> #2
    |> Proof.using_facts facts
    |> pair subgoal_focus
  end

end

val opt_fact_binding =
  Scan.optional (Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty)
    Binding.empty_atts

val for_params =
  Scan.optional
    (\<^keyword>\<open>for\<close> |--
      Parse.!!! ((Scan.option Parse.dots >> is_some) --
        (Scan.repeat1 (Parse.maybe_position Parse.name_position))))
    (false, [])

val schematic_subgoal_cmd = gen_schematic_subgoal Attrib.attribute_cmd

in

(** schematic_subgoal command **)
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>schematic_subgoal\<close>
    "focus on first subgoal within backward refinement, without instantiating schematic vars"
    (opt_fact_binding -- (Scan.option (\<^keyword>\<open>premises\<close> |-- Parse.!!! opt_fact_binding)) --
      for_params >> (fn ((a, b), c) =>
        Toplevel.proofs (Seq.make_results o Seq.single o #2 o schematic_subgoal_cmd a b c)))


end
