structure Elaboration = struct

(** Tracing **)

fun probe (n: int) ctxt ts =
  let
    val _ = tracing (
      "======== Syntax phase level " ^ @{make_string} n ^ " ========" ^
      "\nTerms\n-----\n" ^
      (space_implode "\n" (map (fn t => "\<^item> " ^  @{make_string} t) ts))
    )
  in
    ts
  end

(** Prep phase **)

fun iargs_to_vars idx tm =
  let
    fun conv (Const (\<^const_name>\<open>iarg\<close>, _) $ Abs (name, _, Const (\<^const_name>\<open>idummy\<close>, T))) =
          Var (("*" ^ name, idx), T)
      | conv (t $ u) = conv t $ conv u
      | conv (Abs (x, T, t)) = Abs (x, T, conv t)
      | conv t = t
  in
    conv tm
  end

fun prep_holes ctxt =
  let
    fun expand i head args =
      let
        fun comb head' = list_comb (iargs_to_vars i head', args)
        fun betapplys head' = Term.betapplys (iargs_to_vars i head', args)
      in
        case head of
          Abs (x, T, t) => list_comb (iargs_to_vars i (Abs (x, T, expand i t [])), args)
        | _ =>
          (case Symtab.lookup (Implicits.implicit_defs ctxt) (Term.term_name head) of
            SOME (t, def) =>
              betapplys (Envir.expand_atom (Term.fastype_of head) (Term.fastype_of t, def))
          | NONE => comb head)
      end
  in
    Lib.fold_aterms expand
  end


end
