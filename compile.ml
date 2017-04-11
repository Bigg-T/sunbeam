open Types
open Printf
open Instruction
open Expr
open Pretty
open BatUref
open Optimize

(* Add or change these constants as needed *)
(* let err_COMP_NOT_NUM   = 1
   let err_ARITH_NOT_NUM  = 2
   let err_LOGIC_NOT_BOOL = 3
   let err_IF_NOT_BOOL    = 4
   let err_OVERFLOW       = 5
   let err_GET_NOT_TUPLE  = 6
   let err_GET_LOW_INDEX  = 7
   let err_GET_HIGH_INDEX = 8
   let err_INDEX_NOT_NUM  = 9 *)

let err_COMP_NOT_NUM   = 1
let err_ARITH_NOT_NUM  = 2
let err_LOGIC_NOT_BOOL = 3
let err_IF_NOT_BOOL    = 4
let err_OVERFLOW       = 5
let err_GET_NOT_TUPLE  = 6
let err_GET_LOW_INDEX  = 7
let err_GET_HIGH_INDEX = 8
let err_INDEX_NOT_NUM  = 9
(* err_OUT_OF_MEMORY = 10 *)
let err_INDEX_OUT_OF_BOUNDS = 11
let err_ARITY_MISMATCH = 12
let err_IF_NOT_TUPLE = 13


let const_true = HexConst (0xFFFFFFFF)
let const_false = HexConst(0x7FFFFFFF)
let bool_mask = HexConst(0x80000000)
let tag_as_bool = HexConst(0x00000001)


let end_lambda_body_label = "end_lambda_body_"

type 'a envt = (string * 'a) list;;
type senvt = (string * (int * string list)) list;; (* struct env *)

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
    List.for_all (fun (_, _, e, _) -> is_anf e) binds
    && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e
and is_imm e =
  match e with
  | ENumber _ -> true
  | EBool _ -> true
  | EId _ -> true
  | _ -> false
;;


(* FINISH THIS FUNCTION WITH THE WELL-FORMEDNESS FROM FER-DE-LANCE *)
let well_formed (p : (Lexing.position * Lexing.position) program) builtins struct_env: exn list =
  let rec wf_E e (env : sourcespan envt) =
    match e with
    | EBool _ -> []
    | ENumber(n, loc) ->
      if n > 1073741823 || n < -1073741824 then [Overflow(n, loc)] else []
    | EId (x, loc) ->
      (try ignore (List.assoc x env); []
       with Not_found ->
         [UnboundId(x, loc)])
    | EPrim1(_, e, _) -> wf_E e env
    | EPrim2(_, l, r, _) -> wf_E l env @ wf_E r env
    | EIf(c, t, f, _) -> wf_E c env @ wf_E t env @ wf_E f env
    | ETuple(vals, _) -> List.concat (List.map (fun e -> wf_E e env) vals)
    | EGetItem(tup, idx, _) -> wf_E tup env @ wf_E idx env
    | ESetItem(tup, idx, rhs, _) -> wf_E tup env @ wf_E idx env @ wf_E rhs env
    | EGetItemExact(tup, idx, _) -> wf_E tup env
    | ESetItemExact(tup, idx, rhs, _) -> wf_E tup env @ wf_E rhs env
    | ESeq(stmts, _) -> List.flatten (List.map (fun s -> wf_E s env) stmts)
    | ELet(binds, body, _) ->
      let rec dupe x binds =
        match binds with
        | [] -> None
        | (y, _, _, loc)::_ when x = y -> Some loc
        | _::rest -> dupe x rest in
      let check_scheme_typ_in_env id (env : sourcespan envt) loc : exn list =
        if (List.mem_assq id env) then [] else [UnboundId(id, loc)] in
      let rec process_type t (env : sourcespan envt) loc : exn list =
        match t with
          | TyCon c -> []
          | TyVar id -> check_scheme_typ_in_env id env loc
          | TyArr (typ_list, ret_typ) ->
            (List.concat (List.map (fun x -> (process_type x env loc)) typ_list))
            @
            (process_type ret_typ env loc)
          | TyTup typ_list ->
            (List.concat (List.map (fun x -> (process_type x env loc)) typ_list))
      and process_schemes rem_schemes (env : sourcespan envt) loc : exn list =
        match rem_schemes with
        | None -> []
        | Some (lst, t) -> process_type t env loc in
      let rec process_binds rem_binds (env : sourcespan envt) =
        match rem_binds with
        | [] -> (env, [])
        | (x, topt, e, loc)::rest ->
          let shadow =
            match dupe x rest with
            | Some where -> [DuplicateId(x, where, loc)]
            | None ->
              try
                let existing = List.assoc x env in [ShadowId(x, loc, existing)]
              with Not_found -> [] in
          let scheme_errs = process_schemes topt env loc in
          let errs_e = wf_E e env in
          let new_env = (x, loc)::env in
          let (newer_env, errs) = process_binds rest new_env in
          (newer_env, (scheme_errs @ shadow @ errs_e @ errs)) in
      let (env2, errs) = process_binds binds env in
      errs @ wf_E body env2
    | ELetRec(binds, body, _) -> []
      (* type 'a bind = (string * scheme option * 'a expr * 'a) *)
      (* TODO fix types in well_formed letrec *)
      (* let rec check_letrec_binds binds =
        begin match binds with
        | [] -> []
        | (id, _, ((ELambda(_, _, _)) as e), _)::rest ->
          (wf_E e (id::env)) @ (check_letrec_binds rest)
        | (id, _, _, loc)::rest ->
          [LetRecNonFunction((id, loc))]
        end in
      let args = List.map (fun (id, _, _, _) -> id) binds in
      (check_letrec_binds binds) @ (wf_E body (args @ env)) *)
    | ELambda(args, body, _) ->
      wf_E body (args @ env)
    | EApp(func, args, loc) ->
      (wf_E func env) @ List.concat (List.map (fun e -> wf_E e env) args)
    | EStructInst(name, structname, fieldvals, loc) ->
      let name_shadow =
        if (List.mem_assoc name env)
        then [ShadowId(name, loc, (List.assoc name env))]
        else [] in
      let structname_existence =
        (printf "%s" structname);
        if (List.mem_assoc structname struct_env)
        then []
        else [UnboundId(name, loc)] in (* TODO could make unboundstruct *)
      let fieldval_errs = List.flatten (List.map (fun f -> (wf_E f env)) fieldvals) in
      name_shadow @ structname_existence @ fieldval_errs
    | EStructGet(structname, fieldname, inst, loc) ->
      [] (* TODO add wfn for EStructInst *)
  in
  match p with
  | Program(dstructs, prog_bod, _) -> wf_E prog_bod builtins (*TODO add wfn for structs*)
;;


type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list
;;

let rec untag_dstruct s =
  match s with
  | DStruct(name, fields, _) ->
    DStruct(name, List.map (fun (a, _) -> (a, ())) fields, ())
;;
let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program(dstructs, body, _) ->
      AProgram((List.map untag_dstruct dstructs), helpA body, ())
  (* let rec helpP (p : tag program) : unit aprogram = helpA p *)
  and helpC (e : tag expr) : (unit cexpr * unit anf_bind list) =
    match e with
    | EPrim1(op, arg, _) ->
      let (arg_imm, arg_setup) = helpI arg in
      (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
      let (left_imm, left_setup) = helpI left in
      let (right_imm, right_setup) = helpI right in
      (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
      let (cond_imm, cond_setup) = helpI cond in
      (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ESeq([], _) -> failwith "Impossible by syntax"
    | ESeq([stmt], _) -> helpC stmt
    | ESeq(fst :: rest, tag) ->
      let (fst_ans, fst_setup) = helpC fst in
      let (rest_ans, rest_setup) = helpC (ESeq(rest, tag)) in
      (rest_ans, fst_setup @ [BSeq fst_ans] @ rest_setup)
    | ELet([], body, _) -> helpC body
    | ELet((bind, _, exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpC exp in
      let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, _) ->
      let (names, new_binds_setup) = List.split (List.map (fun (name, _, rhs, _) -> (name, helpC rhs)) binds) in
      let (new_binds, new_setup) = List.split new_binds_setup in
      let (body_ans, body_setup) = helpC body in
      (body_ans, (BLetRec (List.combine names new_binds)) :: body_setup)
    | ELambda(args, body, _) ->
      (CLambda(List.map fst args, helpA body, ()), [])
    | EApp(func, args, _) ->
      let (new_func, func_setup) = helpI func in
      let (new_args, new_setup) = List.split (List.map helpI args) in
      (CApp(new_func, new_args, ()), func_setup @ List.concat new_setup)
    | ETuple(args, _) ->
      let (new_args, new_setup) = List.split (List.map helpI args) in
      (CTuple(new_args, ()), List.concat new_setup)
    | EGetItem(tup, idx, _) ->
      let (tup_imm, tup_setup) = helpI tup in
      let (idx_imm, idx_setup) = helpI idx in
      (CGetItem(tup_imm, idx_imm, ()), tup_setup @ idx_setup)
    | ESetItem(tup, idx, rhs, _) ->
      let (tup_imm, tup_setup) = helpI tup in
      let (idx_imm, idx_setup) = helpI idx in
      let (rhs_imm, rhs_setup) = helpI rhs in
      (CSetItem(tup_imm, idx_imm, rhs_imm, ()), tup_setup @ idx_setup @ rhs_setup)
    | EStructInst(name, structname, fieldvals, _) ->
      let (new_fieldvals, new_setup) = List.split (List.map helpI fieldvals) in
      (CStructInst(name, structname, new_fieldvals, ()), List.concat new_setup)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])

    | EPrim1(op, arg, tag) ->
      let tmp = sprintf "unary_%d" tag in
      let (arg_imm, arg_setup) = helpI arg in
      (ImmId(tmp, ()), arg_setup @ [BLet(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
      let tmp = sprintf "binop_%d" tag in
      let (left_imm, left_setup) = helpI left in
      let (right_imm, right_setup) = helpI right in
      (ImmId(tmp, ()), left_setup @ right_setup @ [BLet(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
      let tmp = sprintf "if_%d" tag in
      let (cond_imm, cond_setup) = helpI cond in
      (ImmId(tmp, ()), cond_setup @ [BLet(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(func, args, tag) ->
      let tmp = sprintf "app_%d" tag in
      let (new_func, func_setup) = helpI func in
      let (new_args, new_setup) = List.split (List.map helpI args) in
      (ImmId(tmp, ()), (func_setup @ List.concat new_setup) @ [BLet(tmp, CApp(new_func, new_args, ()))])
    | ESeq([], _) -> failwith "Impossible by syntax"
    | ESeq([stmt], _) -> helpI stmt
    | ESeq(fst :: rest, tag) ->
      let (fst_ans, fst_setup) = helpC fst in
      let (rest_ans, rest_setup) = helpI (ESeq(rest, tag)) in
      (rest_ans, fst_setup @ [BSeq fst_ans] @ rest_setup)
    | ELet([], body, _) -> helpI body
    | ELet((bind, _, exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpC exp in
      let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, tag) ->
      let tmp = sprintf "lam_%d" tag in
      let (names, new_binds_setup) = List.split (List.map (fun (name, _, rhs, _) -> (name, helpC rhs)) binds) in
      let (new_binds, new_setup) = List.split new_binds_setup in
      let (body_ans, body_setup) = helpC body in
      (ImmId(tmp, ()), (List.concat new_setup)
                       @ [BLetRec (List.combine names new_binds)]
                       @ body_setup
                       @ [BLet(tmp, body_ans)])
    | ELambda(args, body, tag) ->
      let tmp = sprintf "lam_%d" tag in
      (ImmId(tmp, ()), [BLet(tmp, CLambda(List.map fst args, helpA body, ()))])
    | ETuple(args, tag) ->
      let tmp = sprintf "tup_%d" tag in
      let (new_args, new_setup) = List.split (List.map helpI args) in
      (ImmId(tmp, ()), (List.concat new_setup) @ [BLet(tmp, CTuple(new_args, ()))])
    | EGetItem(tup, idx, tag) ->
      let tmp = sprintf "get_%d" tag in
      let (tup_imm, tup_setup) = helpI tup in
      let (idx_imm, idx_setup) = helpI idx in
      (ImmId(tmp, ()), tup_setup @ idx_setup @ [BLet(tmp, CGetItem(tup_imm, idx_imm, ()))])
    | ESetItem(tup, idx, rhs, tag) ->
      let tmp = sprintf "set_%d" tag in
      let (tup_imm, tup_setup) = helpI tup in
      let (idx_imm, idx_setup) = helpI idx in
      let (rhs_imm, rhs_setup) = helpI rhs in
      (ImmId(tmp, ()), tup_setup @ idx_setup @ rhs_setup @ [BLet(tmp, CSetItem(tup_imm, idx_imm, rhs_imm, ()))])
    | EGetItemExact(tup, idx, tag) ->
      let tmp = sprintf "get_%d" tag in
      let (tup_imm, tup_setup) = helpI tup in
      (ImmId(tmp, ()), tup_setup @ [BLet(tmp, CGetItem(tup_imm, ImmNum(idx, ()), ()))])
    | ESetItemExact(tup, idx, rhs, tag) ->
      let tmp = sprintf "set_%d" tag in
      let (tup_imm, tup_setup) = helpI tup in
      let (rhs_imm, rhs_setup) = helpI rhs in
      (ImmId(tmp, ()), tup_setup @ rhs_setup @ [BLet(tmp, CSetItem(tup_imm, ImmNum(idx, ()), rhs_imm, ()))])
    | EStructInst(name, structname, fieldvals, tag) ->
      let tmp = sprintf "makestruct_%d" tag in
      let (new_fieldvals, new_setup) = List.split (List.map helpI fieldvals) in
      (ImmId(tmp, ()), (List.concat new_setup) @ [BLet(tmp, CStructInst(name, structname, new_fieldvals, ()))])
    | EStructGet(structname, fieldname, inst, tag) ->
      let tmp = sprintf "structget_%d" tag in
      let (inst_imm, inst_setup) = helpI inst in
      (ImmId(tmp, ()), inst_setup @ [BLet(tmp, CStructGet(structname, fieldname, inst_imm, ()))])

  and helpA e : unit aexpr =
    let (ans, ans_setup) = helpC e in
    List.fold_right
      (fun bind body ->
         match bind with
         | BSeq(exp) -> ASeq(exp, body, ())
         | BLet(name, exp) -> ALet(name, exp, body, ())
         | BLetRec(names) -> ALetRec(names, body, ()))
      ans_setup (ACExpr ans)
  in
  helpP p
;;


let free_vars (e : 'a aexpr) : string list =
  let rec helpA (bound : string list) (e : 'a aexpr) : string list =
    match e with
    | ASeq(fst, rest, _) ->
      helpC bound fst @ helpA bound rest
    | ALet(name, binding, body, _) ->
      (helpC bound binding) (* all the free variables in the binding, plus *)
      (* all the free variables in the body, except the name itself *)
      @ (helpA (name :: bound) body)
    | ALetRec(bindings, body, _) ->
      let names = List.map fst bindings in
      let new_bound = (names @ bound) in
      (helpA new_bound body) @ List.flatten (List.map (fun binding -> helpC new_bound (snd binding)) bindings)
    | ACExpr c -> helpC bound c
  and helpC (bound : string list) (e : 'a cexpr) : string list =
    match e with
    | CLambda(args, body, _) ->
      helpA (args @ bound) body
    | CIf(cond, thn, els, _) ->
      helpI bound cond @ helpA bound thn @ helpA bound els
    | CPrim1(_, arg, _) -> helpI bound arg
    | CPrim2(_, left, right, _) -> helpI bound left @ helpI bound right
    | CApp(fn, args, _) ->
      (helpI bound fn) @ (List.flatten (List.map (fun arg -> helpI bound arg) args))
    | CTuple(vals, _) -> List.flatten (List.map (fun v -> helpI bound v) vals)
    | CGetItem(tup, idx, _) -> helpI bound tup @ helpI bound idx
    | CSetItem(tup, idx, rhs, _) -> helpI bound tup @ helpI bound idx @ helpI bound rhs
    | CImmExpr i -> helpI bound i
  and helpI (bound : string list) (e : 'a immexpr) : string list =
    match e with
    | ImmId(name, _) ->
      (* a name is free if it is not bound *)
      if List.mem name bound then [] else [name]
    | _ -> []
  in List.sort_uniq String.compare (helpA [] e)
;;

let reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  [
    IMov(Reg(EAX), LabelContents("HEAP_END"));
    ISub(Reg(EAX), Const(size));
    ICmp(Reg(EAX), Reg(ESI));
    IJge(ok);
    IPush(Reg(ESP)); (* stack_top in C *)
    IPush(Reg(EBP)); (* first_frame in C *)
    IPush(Const(size)); (* bytes_needed in C *)
    IPush(Reg(ESI)); (* alloc_ptr in C *)
    ICall(Label("try_gc"));
    IAdd(Reg(ESP), Const(16)); (* clean up after call *)
    (* assume gc success if returning here, so EAX holds the new ESI value *)
    IMov(Reg(ESI), Reg(EAX));
    ILabel(ok);
  ]
;;


let rec is_in_env ls x =
  match ls with
  | [] -> false
  | y::rest ->
    if y = x then true else is_in_env rest x
;;


let rec is_in_tup_list ls x =
  match ls with
  | [] -> false
  | (name, v)::rest ->
    if name = x then true else is_in_tup_list rest x
;;


let rec get_tup_in_env ls x =
  match ls with
  | [] -> []
  | (name, v)::rest ->
    if name = x then [(name, v)] else get_tup_in_env rest x
;;


let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y,v)::rest ->
    if y = x then v else find rest x

let rec add_to_set (s : string) (l : string list) : string list =
  if (is_in_env l s) then l else s::l
;;

let count_vars e =
  let rec helpA e =
    match e with
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ACExpr e -> helpC e
    (* | ALetRec(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body)) *)
    | ALetRec(binds, body, tag) -> 1 + (max (List.fold_left (+) 0 (List.map (fun (_, bind) -> (helpC bind)) binds)) (helpA body))

      (*TODO complete count_vars for letrec *)

      (* failwith "not yet implemented" *)
    | ASeq (cexp, aexp, tag) ->
      1 + (max (helpC cexp) (helpA aexp))
      (* failwith "!!!" *)
  (* failwith "not yet implemented" *)
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in helpA e

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))


let rec get_struct_field_idx fieldname fields idx : int =
  match fields with
  | [] -> failwith "Invalid fieldname"
  | first::rest when (fieldname = first) -> idx
  | first::rest -> get_struct_field_idx fieldname rest (idx + 1)

(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT -- THE ONLY NEW CODE IS CSetItem and ALet *)
(* let compile_fun name args body =
   ([],[],[])
   (* failwith "NYI: compile_fun" *)
*)
let rec compile_fun fun_name args e struct_env : (instruction list * instruction list * instruction list) =
  let args_env = List.mapi (fun i a -> (a, RegOffset(word_size * (i + 2), EBP))) args in
  let compiled = (compile_aexpr e 1 args_env (List.length args) true struct_env) in
  let count_local_vars = count_vars e in
  (* let optimized = optimize compiled in (*causing problem because some invarient are broken*) *)
  (([
      ILabel(fun_name);
      ILineComment("Function prologue");
      IPush(Reg(EBP));
      IMov(Reg(EBP), Reg(ESP))
    ]
      @ replicate (IPush(Sized(DWORD_PTR, Const(0)))) count_local_vars),
   ([ ILineComment("Function body") ]
    (* @ optimized), (*causing problem because some invarient are broken*) *)
    @ compiled),
   [
     ILineComment("Function epilogue");
     IMov(Reg(ESP), Reg(EBP));
     IPop(Reg(EBP));
     IInstrComment(IRet, sprintf "End of %s" fun_name)
   ])
and compile_lambda args lambda_body tag env struct_env =
  let env_str_list = List.map ((fun (x, _) -> x)) env in
  let rec is_contain_string l str =
    match l with
    | [] -> false
    | f::r when f = str -> true
    | _::r -> is_contain_string r str in
  let free_list : string list =
    (* free_vars lambda_body *)
    let free_with_args = free_vars lambda_body in
    let rec filter_args args_list acc =
      match args_list with
      | [] -> acc
      | first :: rest when (is_contain_string args first) -> filter_args rest acc
      | first :: rest -> filter_args rest (first::acc)
    in List.rev (filter_args free_with_args []) in
  (* in (filter_args free_with_args []) in *)
  let rec free_vars_env free_list full_env =
    match free_list with
    | [] -> []
    | name::rest ->
      if (is_in_tup_list full_env name)
      then (get_tup_in_env full_env name) @ (free_vars_env rest full_env)
      else (free_vars_env rest full_env) in
  let padding = ((((List.length free_list) + 2) * 4) mod 8) in
  let next_available_esi =
    if (((((List.length free_list) + 2) * 4) mod 8) == 0)
    then ((List.length free_list) + 2) * 4 else (((List.length free_list) + 2) * 4) + 4 in
  let rec set_up_closure_on_stack free_env acc =
    match free_env with
    | [] -> []
    | (_, offset) :: rest ->
      [
        IInstrComment(IMov(Reg(EAX), RegOffset(8, EBP)), "The address of closure_heap");
        IInstrComment(IAnd(Reg(EAX), HexConst(0xFFFFFFF8)), "untag The address of closure_heap");
        IInstrComment(IMov(Reg(EDX), RegOffset((word_size * (acc + 2)), EAX)), "Move the first freevar to stack");
        IMov(offset, Reg(EDX));
      ] @ set_up_closure_on_stack rest (acc + 1)
  in
  let args_env = List.mapi (fun i a -> (a, RegOffset(word_size * (i + 3), EBP))) args in
  let compiled = (compile_aexpr lambda_body ((List.length free_list) + 1) ((free_vars_env free_list env ) @ args_env) ((List.length args)) true struct_env) in
  let count_local_vars = count_vars lambda_body in
  let rec add_free_var_heap (free_list : string list) (next_offset : int) : (instruction list) =
    match free_list with
    | [] -> if (padding = 1) then [IMov(RegOffset(word_size * (next_offset + 2), ESI), (Sized(DWORD_PTR, HexConst(0xdead1eaf))))] else []
    | first :: rest ->
      [
        IMov(Reg(EDX), (find env first));
        IMov(RegOffset(word_size * (next_offset + 2), ESI), (Sized(DWORD_PTR, Reg(EDX))));
      ] @ (add_free_var_heap rest (next_offset + 1))

  in
  (* let optimized = optimize compiled in *)
  let rec debug_env_str_list env =
    match env with
    | [] -> " |DONEEE| "
    | (name, v) :: r -> name ^ "_" ^ (arg_to_asm v)^ " " ^ (debug_env_str_list r)
  in
  let str_list_str str_list = List.fold_left ((fun x y -> x ^ " " ^ y)) " " str_list in
  (([
      (* TODO not quite right, you'll want this jump to come before the function name, if it has one *)
      IJmp(end_lambda_body_label ^ string_of_int tag); (* TODO but you're jumping over where you save the ESP :( *)
      ILabel("exec_lambda_body_" ^ string_of_int tag);
      ILineComment("Function prologue");
      IPush(Reg(EBP));
      IMov(Reg(EBP), Reg(ESP))
    ]
      @ replicate (IPush(Sized(DWORD_PTR, Const(0)))) (count_local_vars + (List.length free_list))),
   ([
     ILineComment("Function body");
     ILineComment("___________________________________Free Var: " ^ str_list_str free_list ^ " length: " ^string_of_int count_local_vars);

     ILineComment("___________________________________ENV Var: " ^ (debug_env_str_list env));
   ]
     (* @ optimized), *)
     @ (set_up_closure_on_stack (free_vars_env free_list env) 0) @ compiled),
   (* @ compiled), *)
   [
     ILineComment("Function epilogue");
     IMov(Reg(ESP), Reg(EBP));
     IPop(Reg(EBP));
     ILineComment("End of lambda");
     IRet;
   ] @
   (* @ (reserve (((List.length free_list) + 2 + padding) * 4) tag) @ *) (*TODO need to put gc back to lambda*)
   [
     (* creating the lambda/allocation of closure_heap *)
     ILabel(end_lambda_body_label ^ string_of_int tag);
     IMov(Reg(EAX), Reg(ESI)); (* allocate a function tuple *)
     IOr(Reg(EAX), HexConst(0x00000005)); (* tag it as a function tuple *)
     IMov(RegOffset(0, ESI), (Sized(DWORD_PTR, Const(((List.length free_list) lsl 1))))); (* set the arity of the function *)
     IMov(RegOffset(4, ESI), (SizedLabel(DWORD_PTR, ("exec_lambda_body_" ^ string_of_int tag)))); (* get the address of the first instruction of the lambda body *)
   ]
   @ (add_free_var_heap free_list 0)
   @
   [
     IAdd(Reg(ESI), Const(next_available_esi)); (* restore the ESI so it represents the next available spot *)
     (* IAdd(Reg(ESI), HexConst(0x00000010)); (* restore the ESI so it represents the next available spot *) *)
     ILineComment("$______________END___lambda_allocation" ^ string_of_int tag)
   ])
and mov_if_needed dest src =
  if dest = src then []
  else [ IMov(dest, src) ]
and check_num err arg =
  [
    ITest(Sized(DWORD_PTR, arg), HexConst(0x00000001));
    IJnz(err)
  ]
and check_nums err left right = check_num err left @ check_num err right
and check_bool err scratch arg =
  (mov_if_needed scratch arg) @
  [
    IAnd(scratch, HexConst(0x00000007));
    ICmp(scratch, HexConst(0x00000007));
    IJne(err)
  ]
and check_bools err scratch left right = check_bool err scratch left @ check_bool err scratch right
and check_overflow err =
  [
    IJo(err);
  ]
and check_arity err arity_reg num_args =
  (* TODO *)
  [
    ICmp(arity_reg, num_args);
    IJne(err);
  ]
and check_tuple err value =
  [
    IMov(Reg(EDX), value);
    IAnd(Reg(EDX), Const(0x00000007));
    ICmp(Reg(EDX), Const(0x00000001));
    IJne(err);
  ]
and check_low_index err tup_addr idx_reg =
  [
    ITest(idx_reg, HexConst(80000000));
    IJnz(err);
  ]
and check_high_index err tup_addr idx_reg =
  [
    IInstrComment(ICmp(idx_reg, RegOffset(0, tup_addr)), "compare given index with tuple length");
    IJge(err);
  ]
    (* TODO  use the low_index, high_index error messages*)
and check_out_of_bounds err tup_addr idx_reg =
  [
    ITest(idx_reg, HexConst(80000000));
    IJnz(err);
    IInstrComment(ICmp(idx_reg, RegOffset(0, tup_addr)), "compare given index with tuple length");
    IJge(err);
  ]
and compile_aexpr (e : tag aexpr) (si : int) (env : arg envt) (num_args : int) (is_tail : bool) (struct_env : senvt) : instruction list =
  match e with
  | ALet(id, e, body, tag) ->
    printf "let id: %s\n" id;
    let create_lambda_label =
      begin match e with
        | CLambda(args, body, l_tag) ->
          [IJmp(end_lambda_body_label ^ string_of_int l_tag);
           ILabel(id);
           IJmp("exec_lambda_body_" ^ string_of_int l_tag);]
        | _ -> []
      end in
    let prelude = compile_cexpr e (si + 1) env num_args false struct_env in
    let body = compile_aexpr body (si + 1) ((id, RegOffset(~-word_size * si, EBP))::env) num_args is_tail struct_env in
    [ILineComment("$_________________START___let_" ^ string_of_int tag)]
    @ create_lambda_label
    (* @  [ILineComment("$_________________PRELUDE___let_" ^ string_of_int tag)] *)
    @ prelude
    @ [ILineComment("$_________________FFFFFFF___let_" ^ string_of_int tag)]
    @ [ IMov(RegOffset(~-word_size * si, EBP), Reg(EAX)) ]
    @ body
    @ [ILineComment("$_________________END___let_" ^ string_of_int tag)]
  (* @ ILineComment("----end of let");] *)
  | ACExpr e -> compile_cexpr e si env num_args is_tail struct_env
  | ALetRec(binds, body, tag) ->
    let create_lambda_label id e =
      begin match e with
        | CLambda(args, e, l_tag) ->
          [IJmp(end_lambda_body_label ^ string_of_int l_tag);
           ILabel(id);
           IJmp("exec_lambda_body_" ^ string_of_int l_tag);]
        | _ -> failwith "only allow lambda to be bound with"
      end in
    let rec prelude_fn binds next_si =
      begin match binds with
        | [] -> ([], []) (* (instructions, env) *)
        | (id, e)::rest ->
          let (rest_instr, rest_env) = prelude_fn rest (next_si + 1) in
          let prelude = (compile_cexpr e next_si ((id, RegOffset(~-word_size * (next_si - 1), EBP))::env) num_args false struct_env) in
          (
            (
              [ILineComment("$_________________START___letRECCCC______bindinnnng_preludeeeeee_" ^ id ^ string_of_int tag)]
              @ create_lambda_label id e
              @ prelude
              @
              [
                IInstrComment(IMov(Reg(EDX), Reg(EAX)), "save EAX before fixing up the closure for letrec");
                IAnd(Reg(EAX), HexConst(0xFFFFFFF8));
                IMov(RegOffset(8, EAX), Reg(EDX)); (* this assumes that the first free var should be the closure address *)
                IInstrComment(IMov(Reg(EAX), Reg(EDX)), "restore EAX after fixing up the closure for letrec");
              ]
              @ [ILineComment("$_________________END___letRECCCC______bindinnnng_preludeeeeee_" ^ id ^ string_of_int tag)]
              @ [ IMov(RegOffset(~-word_size * (next_si - 1), EBP), Reg(EAX)) ]
              @ rest_instr
            ),
            ((id, RegOffset(~-word_size * (next_si - 1), EBP))::rest_env)
          )
      end in
    let (prelude_instr, prelude_env) = prelude_fn binds (si + 1) in
    let body = compile_aexpr body (si + 1) (prelude_env @ env) num_args is_tail struct_env in
    [ILineComment("$_________________START___letRECCCCCCCCCCCCCCCC_______" ^ string_of_int tag)]
    @ prelude_instr
    @ [ILineComment("$_________________FFFFFFF___let_" ^ string_of_int tag)]
    @ body
    @ [ILineComment("$_________________END___letRECCCCCCCCCCCCCCCC _______________ENDDDDDDDDDD_" ^ string_of_int tag)]
  | ASeq (cexp, aexp, tag) ->
    let compiled_cexp = compile_cexpr cexp (si + 1) env num_args is_tail struct_env in
    let compiled_aexp = compile_aexpr aexp si env num_args is_tail struct_env in
    compiled_cexp @ compiled_aexp
and compile_cexpr (e : tag cexpr) si env num_args is_tail struct_env =
  match e with
  | CPrim1(op, e, tag) ->
    let e_reg = compile_imm e env in
    begin match op with
      | Add1 ->
        (mov_if_needed (Reg EAX) e_reg)
        @ (check_num "err_arith_not_num" (Reg EAX))
        @ [ IAdd(Reg(EAX), Const(2)) ]
        @ (check_overflow "err_overflow")
      | Sub1 ->
        (mov_if_needed (Reg EAX) e_reg)
        @ (check_num "err_arith_not_num" (Reg EAX))
        @ [ IAdd(Reg(EAX), Const(~-2)) ]
        @ (check_overflow "err_overflow")
      | IsBool ->
        (mov_if_needed (Reg EAX) e_reg) @
        [
          IAnd(Reg(EAX), Const(0x00000007));
          ICmp(Reg(EAX), Const(0x00000007));
          IJne("not_bool");
          IMov(Reg(EAX), const_true);
          IJmp("continue_is_bool");
          ILabel("not_bool");
          IMov(Reg(EAX), const_false);
          ILabel("continue_is_bool");
          (* IShl(Reg(EAX), Const(31)); *)
          (* IOr(Reg(EAX), const_false) *)
        ]
      | IsNum ->
        (mov_if_needed (Reg EAX) e_reg) @
        [
          IAnd(Reg(EAX), Const(0x00000001));
          ICmp(Reg(EAX), Const(0x00000000));
          IJne("not_num");
          IMov(Reg(EAX), const_true);
          IJmp("continue_is_num");
          ILabel("not_num");
          IMov(Reg(EAX), const_false);
          ILabel("continue_is_num");
          (* IShl(Reg(EAX), Const(31)); *)
          (* IOr(Reg(EAX), const_false) *)
        ]
      | IsTuple ->
        (mov_if_needed (Reg EAX) e_reg) @
        [
          IAnd(Reg(EAX), Const(0x00000007));
          ICmp(Reg(EDX), Const(0x00000001));
          IJe("is_tuple");
          IMov(Reg(EAX), const_true);
          IJmp("continue_is_tuple");
          ILabel("is_tuple");
          IMov(Reg(EAX), const_false);
          ILabel("continue_is_tuple");
        ]
      (* failwith "Not yet implemented: IsTuple" *)
      | Not ->
        (mov_if_needed (Reg EAX) e_reg)
        @ (check_bool "err_logic_not_bool" (Reg EDX) (Reg EAX))
        @ [ IXor(Reg(EAX), bool_mask) ]
      | Print -> [
          IMov(Reg(EAX), (compile_imm e env));
          IPush(Reg(EAX));
          ICall(Label("print"));
          IAdd(Reg(ESP), Const(4));
        ]
      | PrintStack ->
        (mov_if_needed (Reg EAX) e_reg)
        @ call "print_stack"
          [Sized(DWORD_PTR, Reg(EAX));
           Sized(DWORD_PTR, Reg(ESP));
           Sized(DWORD_PTR, Reg(EBP));
           Sized(DWORD_PTR, Const(num_args))]
    end
  | CPrim2(op, left, right, tag) ->
    let left_reg = compile_imm left env in
    let right_reg = compile_imm right env in
    let arith_op op =
      (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
      @ check_nums "err_arith_not_num" (Reg EAX) (Reg EDX)
      @ [ op (Reg(EAX), Reg(EDX)) ]
      @ check_overflow "err_overflow" in
    let comp_op op =
      let true_label = sprintf "true_%d" tag in
      let done_label = sprintf "done_%d" tag in
      (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
      @ (check_nums "err_comp_not_num" (Reg EAX) (Reg EDX))
      @ [
        IMov(Reg(EAX), left_reg);
        ICmp(Reg(EAX), right_reg);
        IMov(Reg(EAX), const_false);
        op done_label;
        ILabel(true_label);
        IMov(Reg(EAX), const_true);
        ILabel(done_label);
      ] in
    let logic_op op =
      (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
      @ (check_bools "err_arith_not_num" (Reg ECX) (Reg EAX) (Reg EDX))
      @ [
        IMov(Reg(EAX), left_reg);
        op (Reg(EAX), right_reg)
      ]  in
    begin match op with
      | Plus -> arith_op (fun (dest, src) -> IAdd(dest, src))
      | Minus -> arith_op (fun (dest, src) -> ISub(dest, src))
      | Times ->
        (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
        @ check_nums "err_arith_not_num" (Reg EAX) (Reg EDX)
        @ [ ISar(Reg(EAX), Const(1)); IMul(Reg(EAX), Reg(EDX)) ]
        @ check_overflow "err_overflow"
      | Less -> comp_op (fun dest -> IJge dest)
      (* You're encouraged to try generating better code for these comparisons.
            The following code should work for lessthan; generate similar code for the others *)
      (* [
          IMov(Reg(EAX), left_reg);
          ISar(Reg(EAX), Const(1));
          IMov(Reg(EBX), right_reg);
          ISar(Reg(EBX), Const(1));
          ISub(Reg(EAX), Reg(EBX));
          IAnd(Reg(EAX), bool_mask);
          IOr(Reg(EAX), tag_as_bool)
         ] *)
      | Greater -> comp_op (fun dest -> IJle dest)
      | LessEq -> comp_op (fun dest -> IJg dest)
      | GreaterEq -> comp_op (fun dest -> IJl dest)
      | Eq ->
        let true_label = sprintf "true_%d" tag in
        let done_label = sprintf "done_%d" tag in
        (mov_if_needed (Reg EAX) left_reg) @
        [
          ICmp(Reg(EAX), right_reg);
          IMov(Reg(EAX), const_false);
          IJne(done_label);
          ILabel(true_label);
          IMov(Reg(EAX), const_true);
          ILabel(done_label)
        ]
      | And -> logic_op (fun (dest, src) -> IAnd(dest, src))
      | Or -> logic_op (fun (dest, src) -> IOr(dest, src))
    end
  | CIf(cond, thn, els, tag) ->
    let cond_reg = compile_imm cond env in
    let else_label = sprintf "else_%d" tag in
    let end_label = sprintf "end_%d" tag in
    (mov_if_needed (Reg EAX) cond_reg)
    @ (check_bool "err_if_not_bool" (Reg ECX) (Reg EAX))
    @ [
      ICmp(Reg(EAX), const_true);
      IJne(else_label)
    ]
    @ (compile_aexpr thn si env num_args is_tail struct_env)
    @ [ IJmp(end_label); ILabel(else_label) ]
    @ (compile_aexpr els si env num_args is_tail struct_env)
    @ [ ILabel(end_label) ]
  | CImmExpr i -> [ IMov(Reg(EAX), compile_imm i env) ]
  | CApp(funa, args, tag) ->
    (* This implementation ignores tail calls entirely.  Please fix it. *)
    (* TODO need to implement calls... *)
    (* (compile_fun funname args) *)
    let call_instr =
      match funa with
      | ImmId(str, _) ->
        [IMov(Reg(EAX), (compile_imm funa env));]
        @ (call "check_fun_name" [Reg(EAX)])
        @
        [
          (* ISub(Reg(EAX), Const(~-4)); *)
          IInstrComment(IOr(Reg(EAX), HexConst(0x00000005)), "the addr to the starting of closure");
          IInstrComment(IPush(Reg(EAX)), "the addr to the starting of closure");
          IInstrComment(IAnd(Reg(EAX), HexConst(0xFFFFFFF8)), "the addr to the starting of closure");
        ]
        @
        [
          IInstrComment(ICall(RegOffset(4, EAX)), "The address to execute lambda");
        ]
      | _ -> [] in
    let numargs = List.length args in
    let pushargs = List.rev (List.map (fun a -> IPush (Sized(DWORD_PTR, compile_imm a env))) args) in
    [ILineComment("$_________________START___CAPP__" ^ (string_of_int tag))]
    @ pushargs
    @ call_instr
    @
    [
      IAdd(Reg(ESP), HexConst(4*(numargs + 1)));
      ILineComment("$_________________END___CAPP__" ^ string_of_int tag);
    ]
  | CTuple(elts, tag) ->
    let padding = if (((((List.length elts) + 1) * 4) mod 8) == 0) then 0 else 1 in
    (* let padding = ((List.length elts) mod 2) in *)
    let rec allocate_tuple_elts elems idx =
      match elems with
      | [] ->
        let add_in_padding =
          if (padding = 1)
          then [IMov(RegOffset((idx * 4), ESI), (Sized(DWORD_PTR, HexConst(0xdeadface))))]
          else [] in
        add_in_padding @ [IAdd(Reg(ESI), Const((idx + padding) * 4))]
      | first::rest ->
        [
          (* TODO  would be good to only do this move if it's a tuple *)
          IMov(Reg(EDX), (Sized(DWORD_PTR, (compile_imm first env))));
          IInstrComment(IMov(RegOffset((idx * 4), ESI), Reg(EDX)), "move tuple value to address of ESI");
        ]
        @ (allocate_tuple_elts rest (idx + 1))
    in
    (* make the tuple and put it on the heap *)
      (*
      increment value of ESI so that it represents the next available addr on the heap
      and then add on the next value of the tuple
      *)
    (* [IInstrComment(IMov(Reg(EDX), Reg(EAX)), "save EAX before gc")] @ *)
    (reserve (((List.length elts) + 1 + padding) * 4) tag) @
    (* @ [IInstrComment(IMov(Reg(EAX), Reg(EDX)), "restore EAX after gc")] @ *)
    [
      ILineComment("__________________TUPLE_STARTTTT_______________" ^ string_of_int tag);
      (* "allocation step" *)
      IMov(Reg(EAX), Reg(ESI));
      (* IAdd(Reg(ESI), Const(8)); *)
      IInstrComment(IOr(Reg(EAX), Const(1)), "create pointer to tuple");
      (* length of tuple *)
      IInstrComment(IMov(RegOffset(0, ESI), (Sized(DWORD_PTR, (Const((List.length elts) lsl 1))))),
                    "move length of tuple into ESI");
    ]
    @
    (allocate_tuple_elts elts 1)
    @ [ILineComment("print_stack" ^ string_of_int tag);]
  | CGetItem(coll, index, tag) ->
    [
      ILineComment("CGetItem start here" ^ string_of_int tag);
      IMov(Reg(EAX), (compile_imm coll env));
    ]
    @
    (check_tuple "err_if_not_tuple" (Reg(EAX)))
    @
    [
      (* shift right and shift left by 3 to get rid of the 001 tag for a tuple *)
      IInstrComment(ISar(Reg(EAX), Const(3)), "get rid of the 001 tag for a tuple");
      IShl(Reg(EAX), Const(3));

      (* move index into EDX *)
      IMov(Reg(EDX), (compile_imm index env));
    ]
    @
    (check_out_of_bounds "err_index_out_of_bounds" EAX (Reg(EDX)))
    @
    [
      (* get the value at the index in the tuple *)
      IMov(Reg(ECX), RegOffsetReg(EAX, EDX, 2, 4));
      IMov(Reg(EAX), Reg(ECX));

      ILineComment("CGetItem end here" ^ string_of_int tag)
    ]
  | CLambda(args, body, tag) ->
    (* TODO should pass in the pointer to function tuple and the free env based on the distance from the start of the tuple*)
    let (prologue, comp_body, epilogue) = (compile_lambda args body tag env struct_env) in
    let lambda_body = prologue @ comp_body @ epilogue in
    [
      ILineComment("$_________________START___lambda_" ^ string_of_int tag);
    ]
    @
    lambda_body
  | CSetItem(tup, idx, new_elt, tag) ->
    let compiled_new_elt =
      match (compile_imm new_elt env) with
      | RegOffset(_, _) ->
        [
          IMov(Reg(ECX), (compile_imm new_elt env));
          IMov(RegOffsetReg(EAX, EDX, 2, 4), Reg(ECX));
        ]
      | _ -> [IMov(RegOffsetReg(EAX, EDX, 2, 4), Sized(DWORD_PTR, (compile_imm new_elt env)));] in
      (* IMov(RegOffsetReg(EAX, EDX, 2, 4), (compile_imm new_elt env)); *)
    [
      ILineComment("CSetItem start here" ^ string_of_int tag);
      IMov(Reg(EAX), (compile_imm tup env));
    ]
    @
    (check_tuple "err_if_not_tuple" (Reg(EAX)))
    @
    [
      ISar(Reg(EAX), Const(3));
      IShl(Reg(EAX), Const(3));
      IMov(Reg(EDX), (compile_imm idx env));
    ]
    @
    (check_out_of_bounds "err_index_out_of_bounds" EAX (Reg(EDX)))
    @ compiled_new_elt @
    [
      (* IMov(Reg(CL), (compile_imm new_elt env)); *)
      (* IMov(RegOffsetReg(EAX, EDX, 2, 4), Sized(DWORD_PTR, (compile_imm new_elt env))); *)
      (* IMov(RegOffsetReg(EAX, EDX, 2, 4), (compile_imm new_elt env)); *)
      IAdd(Reg(EAX), Const(1));
    ]
  | CStructInst(name, structname, fieldvals, tag) ->
    let (uniq_tag, fieldnames) = List.assoc structname struct_env in
    let padding = if (((((List.length fieldvals) + 2) * 4) mod 8) == 0) then 0 else 1 in
    let rec allocate_struct_fields fieldvals idx =
      match fieldvals with
      | [] ->
        let add_in_padding =
          if (padding = 1)
          then [IMov(RegOffset((idx * 4), ESI), (Sized(DWORD_PTR, HexConst(0xdeadface))))]
          else [] in
        add_in_padding @ [IAdd(Reg(ESI), Const((idx + padding) * 4))]
      | first::rest ->
        [
          IMov(Reg(EDX), (Sized(DWORD_PTR, (compile_imm first env))));
          IInstrComment(IMov(RegOffset((idx * 4), ESI), Reg(EDX)), "move struct value to address of ESI");
        ]
        @ (allocate_struct_fields rest (idx + 1))
    in
    (* make the struct inst and put it on the heap *)
      (*
      increment value of ESI so that it represents the next available addr on the heap
      and then add on the next value of the tuple
      *)
    (reserve (((List.length fieldvals) + 2 + padding) * 4) tag) @
    [
      ILineComment("__________________STRUCT_STARTTTT_______________" ^ string_of_int tag);
      (* "allocation step" *)
      IMov(Reg(EAX), Reg(ESI));
      (* IAdd(Reg(ESI), Const(8)); *)
      IInstrComment(IOr(Reg(EAX), Const(7)), "create pointer to struct inst");
      (* unique struct tag  *)
      IInstrComment(IMov(RegOffset(0, ESI), (Sized(DWORD_PTR, (Const(uniq_tag lsl 1))))),
                    "move unique struct tag into ESI");
      (* length of struct fields *)
      IInstrComment(IMov(RegOffset(4, ESI), (Sized(DWORD_PTR, (Const((List.length fieldvals) lsl 1))))),
                    "move length of struct into ESI");
    ]
    @
    (allocate_struct_fields fieldvals 2)
    @ [ILineComment("print_stack" ^ string_of_int tag);]
  | CStructGet(structname, fieldname, inst, tag) ->
    let (uniq_tag, fieldnames) = List.assoc structname struct_env in
    let field_idx = ImmNum((get_struct_field_idx fieldname fieldnames 0), 0) in
    [
      ILineComment("CStructGet start here" ^ string_of_int tag);
      IMov(Reg(EAX), (compile_imm inst env));
    ]
    @ (* TODO add check_struct, error if not struct *)
    [
      (* shift right and shift left by 3 to get rid of the 111 tag for a struct inst *)
      IInstrComment(ISar(Reg(EAX), Const(3)), "get rid of the 111 tag for a struct inst");
      IShl(Reg(EAX), Const(3));

      (* move index into EDX *)
      IMov(Reg(EDX), (compile_imm field_idx env));
      (* get the value at the index in the struct inst *)
      IMov(Reg(ECX), RegOffsetReg(EAX, EDX, 2, 4));
      IMov(Reg(EAX), Reg(ECX));

      ILineComment("CStructGet end here" ^ string_of_int tag)
    ]
and compile_imm e env =
  match e with
  | ImmNum(n, _) -> Const((n lsl 1))
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)
and call label args =
  let setup = List.rev_map (fun arg -> IPush(Sized(DWORD_PTR, arg))) args in
  let teardown =
    let len = List.length args in
    if len = 0 then []
    else [ IInstrComment(IAdd(Reg(ESP), Const(4 * len)), sprintf "Popping %d arguments" len) ] in
  setup @ [ ICall(Label(label)) ] @ teardown
and optimize instrs =
  match instrs with
  | IMov(Reg(EAX), exp)::IMov(dest, Reg(EAX))::tail -> IMov(Sized(DWORD_PTR, dest), exp)::optimize tail
  | i::tail -> i :: optimize tail
  | [] -> []
;;
(* UPDATE THIS TO HANDLE FIRST-CLASS FUNCTIONS AS NEEDED *)
let call (label : arg) args =
  let setup = List.rev_map (fun arg ->
      match arg with
      | Sized _ -> IPush(arg)
      | _ -> IPush(Sized(DWORD_PTR, arg))) args in
  let teardown =
    let len = List.length args in
    if len = 0 then []
    else [ IInstrComment(IAdd(Reg(ESP), Const(4 * len)), sprintf "Popping %d arguments" len) ] in
  setup @ [ ICall(label) ] @ teardown
;;


let rec make_struct_env (structdefs : 'a dstruct list) (uniq_tag : int) : senvt =
  match structdefs with
  | [] -> []
  | DStruct(name, fields, _)::rest ->
    let field_names = List.map (fun (f,  _) -> f) fields in
    (name, (uniq_tag, field_names))::(make_struct_env rest (uniq_tag + 1))
;;


let compile_prog prog =
  let (structdefs, anfed) =
    match prog with
    | AProgram(dstructs, body, _) -> (dstructs, body) in
  let struct_env = (make_struct_env structdefs 1) in
  let prelude =
    "section .text
extern error
extern print
extern equal
extern check_fun_name
extern is_eight_bit_boundary
extern print_stack
extern print_closure
extern try_gc
extern HEAP_END
extern STACK_BOTTOM
global our_code_starts_here" in
  let suffix = sprintf "
err_comp_not_num:%s
err_arith_not_num:%s
err_logic_not_bool:%s
err_if_not_bool:%s
err_if_not_tuple:%s
err_overflow:%s
err_arity_mismatch:%s
err_get_not_tuple:%s
err_get_low_index:%s
err_get_high_index:%s
err_index_out_of_bounds:%s
err_index_not_num:%s"
      (* If you modified `call` above, then fix these up, too *)
      (to_asm (call (Label "error") [Const(err_COMP_NOT_NUM)]))
      (to_asm (call (Label "error") [Const(err_ARITH_NOT_NUM)]))
      (to_asm (call (Label "error") [Const(err_LOGIC_NOT_BOOL)]))
      (to_asm (call (Label "error") [Const(err_IF_NOT_BOOL)]))
      (to_asm (call (Label "error") [Const(err_OVERFLOW)]))
      (to_asm (call (Label "error") [Const(err_ARITY_MISMATCH)]))
      (to_asm (call (Label "error") [Const(err_GET_NOT_TUPLE)]))
      (to_asm (call (Label "error") [Const(err_GET_LOW_INDEX)]))
      (to_asm (call (Label "error") [Const(err_GET_HIGH_INDEX)]))
      (to_asm (call (Label "error") [Const(err_INDEX_NOT_NUM)]))
      (to_asm (call (Label "error") [Const(err_INDEX_OUT_OF_BOUNDS)]))
      (to_asm (call (Label "error") [Const(err_IF_NOT_TUPLE)]))
  in
  (* $heap is a mock parameter name, just so that compile_fun knows our_code_starts_here takes in 1 parameter *)
  let (prologue, comp_main, epilogue) = compile_fun "our_code_starts_here" ["$heap"] anfed struct_env in
  let heap_start = [
    IInstrComment(IMov(LabelContents("STACK_BOTTOM"), Reg(EBP)), "This is the bottom of our Garter stack");
    ILineComment("heap start");
    IInstrComment(IMov(Reg(ESI), RegOffset(8, EBP)), "Load ESI with our argument, the heap pointer");
    IInstrComment(IAdd(Reg(ESI), Const(7)), "Align it to the nearest multiple of 8");
    IInstrComment(IAnd(Reg(ESI), HexConst(0xFFFFFFF8)), "by adding no more than 7 to it")
  ] in
  let main = (prologue @ heap_start @ comp_main @ epilogue) in

  sprintf "%s%s%s\n" prelude (to_asm main) suffix


let optimize (prog : tag aprogram) (verbose : bool) : tag aprogram =
  let const_prog = atag (const_fold prog) in
  let cse_prog = atag (cse const_prog) in
  let dae_prog = atag (dae cse_prog) in
  let const_prog2 = atag (const_fold dae_prog) in
  let cse_prog2 = atag (cse const_prog2) in
  let dae_prog2 = atag (dae cse_prog2) in
  (if verbose
   then begin
       printf "Const/tagged:\n%s\n" (string_of_aprogram const_prog);
       printf "CSE/tagged:\n%s\n" (string_of_aprogram cse_prog);
       printf "DAE/tagged:\n%s\n" (string_of_aprogram dae_prog)
     end
   else ());
  dae_prog2
;;


let compile_to_string prog : (exn list, string) either =
  let (structdefs, prog_body) =
    match prog with
    | Program(dstructs, body, _) ->
      (dstructs, body) in
  let struct_env = (make_struct_env structdefs 1) in
  let env = [ (* DBuiltin("equal", 2) *) ] in
  let errors = (well_formed prog env struct_env) in
  match errors with
  | [] ->
    let tagged : tag program = tag prog in
    let anfed : tag aprogram = atag (anf tagged) in
    let optimized : tag aprogram = (atag (optimize anfed true)) in
    (* printf "Prog:\n%s\n" (ast_of_prog prog);
    printf "Tagged:\n%s\n" (format_prog tagged string_of_int); *)
    printf "ANFed/tagged:\n%s\n" (string_of_aprogram anfed);
    Right(compile_prog optimized)
    (* Right(compile_prog anfed) *)
  | _ -> Left(errors)
