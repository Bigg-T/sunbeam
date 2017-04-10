open Types
open Printf
open Instruction
open Expr
open Pretty
open BatUref

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


let rec purity_env (prog : tag aprogram) : (string * bool) list =
  match prog with
  | AProgram(dstructs, body, _) ->
    let (_, env) = helpA body [] in env
and helpA (aexp : tag aexpr) (pure_env : (string * bool) list) : bool * (string * bool) list =
  (* is the given expression pure or not?
     Also, update ans with any bindings you encounter. *)
  match aexp with
  | ASeq(fst, rest, _) ->
    let args_env =
      begin match fst with
      | CLambda(args, body, _) ->
        List.map (fun x -> (x, true)) args
      | _ -> []
      end in
    let (f, f_env) = helpC fst (args_env @ pure_env) in
    let (r, r_env) = helpA rest pure_env in
    ((f && r), (pure_env @ f_env @ r_env))
  | ALet(name, binding, body, _) ->
    let (bind_body_env, args_env) = env_for_lambda_body name binding pure_env in
    let (bind, bind_env) = helpC binding (args_env @ pure_env) in
    let new_bind_env =
      begin match binding with
        | CImmExpr(ImmId(a, _)) -> (name, true)::bind_env
        | _ -> (name, bind)::bind_env
      end in
    let (bod, bod_env) = helpA body (bind_body_env @ pure_env @ new_bind_env @ bind_env) in
    (bod, new_bind_env @ bind_body_env @ bod_env @ pure_env)
  | ALetRec(bindings, body, _) ->
    let lambda_body_envs =
      List.flatten
        (List.map
           ((fun (bname, cexp) ->
               let args_env =
                 match cexp with
                 | CLambda(args, body, _) ->
                   List.map (fun x -> (x, true)) args
                 | _ -> [] in
               let (bind, bind_env) = helpC cexp (args_env @ ((bname, false)::((bname ^ "_body"), false)::pure_env)) in
               (bind_env @ ((bname, false)::((bname ^ "_body"), false)::pure_env))))
           bindings) in
    let (bod, bod_env) = helpA body (lambda_body_envs @ pure_env) in
    (bod, lambda_body_envs @ bod_env @ pure_env)
  | ACExpr c ->
    let (c_is_pure, extra_env) = helpC c pure_env in
    (c_is_pure, extra_env @ pure_env)
and helpC (cexp : tag cexpr) (pure_env : (string * bool) list) : bool * (string * bool) list =
  match cexp with
  (* CLambda assumes only pure arguments passed in *)
  | CLambda(args, body, _) ->
    (* TODO we don't currently use b_pure for anything, but probably should *)
    let (b_pure, b_env) = helpA body pure_env in (*if any new env*)
    (false, b_env)
  | CIf(cond, thn, els, _) -> (* the cond is always pure, because the way anf works, all inpure are pulled out to an assigment, time of using it is not pure*)
    let (t_case, t_env) = helpA thn pure_env in
    let (e_case, e_env) = helpA els pure_env in
    ((t_case && e_case), (t_env @ e_env)) (*passed the new evn*)
  | CPrim1(op, arg, _) ->
    begin match op with
      | Print | PrintStack -> (false, [])
      | _ -> ((helpI arg pure_env), [])
    end
  | CPrim2(_, left, right, _) ->
    let lf = helpI left pure_env in
    let rt = helpI right pure_env in
    ((lf && rt), [])
  | CApp(fn, args, _) ->
    begin match fn with
      | ImmId(name, _) ->
        ((List.assoc (name ^ "_body") pure_env), [])
      | _ -> failwith "Impossible"
    end
(* this only looks for purity/impurity in the lambda 1 level deep*)
  | CTuple(vals, _) -> ((false), [])
  | CGetItem(tup, idx, _) -> ((true), [])
  | CSetItem(tup, idx, rhs, _) -> ((false), [])
  | CImmExpr i -> ((helpI i pure_env), [])
and helpI (imm : tag immexpr) (pure_env : (string * bool) list) : bool =
  match imm with
  | ImmNum(n, _) -> true
  | ImmBool(b, _) -> true
  | ImmId(name, _) ->
    (List.assoc name pure_env)
(* doesn't need to check existed, because inorder for id to be use it must existed.
   If not this would of failed in well_formed*)
and env_for_lambda_body name bind pure_env=
  match bind with
  | CLambda(args, body, _) ->
    let args_env = List.map (fun x -> (x, true)) args in
    let (lambda_body, lambda_body_env) = (helpA body (args_env @ pure_env)) in
    ([((name ^ "_body"), lambda_body)], args_env)
  | _ -> ([], [])
and debug_pure_env env =
   match env with
   | [] -> ""
   | (str, boo)::rest -> "Key: " ^ str ^ "  " ^ "val:  " ^ (string_of_bool boo) ^ "\n" ^ (debug_pure_env rest)
;;



let rec string_of_simple s =
  match s with
  | Id s -> s
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Prim1(op, arg) -> sprintf "%s(%s)" (string_of_op1 op) (string_of_simple arg)
  | Prim2(op, left, right) -> sprintf "%s(%s, %s)" (string_of_op2 op) (string_of_simple left) (string_of_simple right)
  | App(f, args) -> sprintf "%s(%s)" (string_of_simple f) (ExtString.String.join ", " (List.map string_of_simple args))
;;
let rec simple_to_cexpr simple =
  let rec s_to_imm s =
    match s with
    | Id n -> ImmId(n, ())
    | Num n -> ImmNum(n, ())
    | Bool b -> ImmBool(b, ())
    | _ -> failwith ("Impossible" ^ (string_of_simple s))
  in
  match simple with
  | Prim1(op, arg) -> CPrim1(op, s_to_imm arg, ())
  | Prim2(op, left, right) -> CPrim2(op, s_to_imm left, s_to_imm right, ())
  | App(f, args) -> CApp(s_to_imm f, List.map s_to_imm args, ())
  | _ -> CImmExpr (s_to_imm simple)
;;
let imm_to_simple i =
  match i with
  | ImmId(n, _) -> Id n
  | ImmNum(n, _) -> Num n
  | ImmBool(b, _) -> Bool b
;;
let cexpr_to_simple_opt cexp =
  match cexp with
  | CPrim1(op, arg, _) -> Some (Prim1(op, imm_to_simple arg))
  | CPrim2(op, left, right, _) -> Some (Prim2(op, imm_to_simple left, imm_to_simple right))
  | CApp(f, args, _) -> Some (App(imm_to_simple f, List.map imm_to_simple args))
  | CImmExpr i -> Some (imm_to_simple i)
  | _ -> None
;;
let rec untag_cexpr (cexp : 'a cexpr) : unit cexpr =
  match cexp with
  | CIf(a, b, c, _) -> CIf((untag_immexpr a), (untag_aexpr b), (untag_aexpr c), ())
  | CPrim1(a, b, _) -> CPrim1(a, (untag_immexpr b), ())
  | CPrim2(a, b, c, _) -> CPrim2(a, (untag_immexpr b), (untag_immexpr c), ())
  | CApp(a, b, _) -> CApp((untag_immexpr a), (List.map untag_immexpr b), ())
  | CTuple(a, _) -> CTuple((List.map untag_immexpr a), ())
  | CGetItem(a, b, _) -> CGetItem((untag_immexpr a), (untag_immexpr b), ())
  | CSetItem(a, b, c, _) -> CSetItem((untag_immexpr a), (untag_immexpr b), (untag_immexpr c), ())
  | CLambda(a, b, _) -> CLambda(a, (untag_aexpr b), ())
  | CImmExpr(a) -> CImmExpr((untag_immexpr a))
and untag_aexpr (aexp : 'a aexpr) : unit aexpr =
  match aexp with
  | ALet(a, b, c, _) -> ALet(a, (untag_cexpr b), (untag_aexpr c), ())
  | ALetRec(a, b, _) -> ALetRec((List.map (fun (name, c) -> (name, (untag_cexpr c))) a), (untag_aexpr b), ())
  | ASeq(a, b, _) -> ASeq((untag_cexpr a), (untag_aexpr b), ())
  | ACExpr(a) -> ACExpr((untag_cexpr a))
and untag_immexpr (imm : 'a immexpr) : unit immexpr =
  match imm with
  | ImmNum(a, _) -> ImmNum(a, ())
  | ImmBool(a, _) -> ImmBool(a, ())
  | ImmId(a, _) -> ImmId(a, ())
and untag_dstruct (dstruct : 'a dstruct) : unit dstruct =
  match dstruct with
  | DStruct(name, fields, _) ->
    DStruct(name, List.map (fun (f, _) -> (f, ())) fields, ())
;;

type simple_env = (string * simple_expr) list

let rec debug_print (env : simple_env) : string =
  match env with
  | [] -> ""
  | (str, sim)::rest ->
    "Key: " ^ str ^ " ; " ^ "value: " ^ (string_of_simple sim) ^ "\n" ^ (debug_print rest)


let rec const_fold (prog : tag aprogram) : unit aprogram =
  match prog with
  | AProgram(dstructs, prog_body, _) ->
    AProgram((List.map untag_dstruct dstructs), (const_fold_a prog_body []), ())
and const_fold_a (aexp : 'a aexpr) (env : simple_env) : unit aexpr =
  match aexp with
  | ACExpr c -> ACExpr(const_fold_c c env)
  | ALet(name, binding, body, _) ->
    let bind_folded = (const_fold_c binding env) in
    let fold_env =
      begin match (cexpr_to_simple_opt bind_folded) with
      | Some s -> ((name, s)::env)
      | None -> env
      end in
    ALet(name, bind_folded, (const_fold_a body fold_env), ())
  | ASeq(cex, aex, _) ->
    ASeq((const_fold_c cex env), (const_fold_a aex env), ())
  | ALetRec(bindings, body, _) ->
    ALetRec((List.map (fun (s, c) -> (s, (const_fold_c c env))) bindings), (const_fold_a body env), ())
and const_fold_c (cexp : 'a cexpr) (env : simple_env) : unit cexpr =
  let simple = cexpr_to_simple_opt cexp in
  match simple with
  | Some s -> let simp = (const_fold_simple s env) in
    (simple_to_cexpr simp)
  | None -> (const_fold_not_simple cexp env)
and const_fold_not_simple (cexp : 'a cexpr) (env : simple_env) : unit cexpr =
  match cexp with
  | CIf(cond, thn, els, _) ->
    CIf((untag_immexpr cond), (const_fold_a thn env), (const_fold_a els env), ())
  | CTuple(vals_list, _) ->
    CTuple((List.map untag_immexpr vals_list), ())
  | CGetItem(tup, idx, _) ->
    CGetItem((untag_immexpr tup), (untag_immexpr idx), ())
  | CSetItem(tup, idx, new_val, _) ->
    CSetItem((untag_immexpr tup), (untag_immexpr idx), (untag_immexpr new_val), ())
  | CLambda(names, body, _) ->
    CLambda(names, (const_fold_a body env), ())
  | _ -> failwith "Not complex"
and const_fold_simple (sexp : simple_expr) (env : simple_env) : simple_expr =
  match sexp with
  | Id(name) ->
    if (List.mem_assoc name env)
    then
      let env_val = (List.assoc name env) in
      begin match (List.assoc name env) with
        | Id(name) -> env_val
        | Bool(b) -> env_val
        | Num(n) -> env_val
        | _ -> sexp
      end
    else sexp
  | Num(n) -> sexp
  | Bool(b) -> sexp
  | Prim1(op, exp) ->
    begin match op, exp with
      | Add1, Num(n) ->  Num(1 + n)
      | Sub1, Num(n) -> Num(n - 1)
      | Not, Bool(b) -> Bool(not(b))
      | IsNum, e ->
        let const_e = (const_fold_simple e env) in
        begin match const_e with
          | Num(n) -> Bool(true)
          | Bool(b) -> Bool(false)
          | _ -> sexp
        end
      | IsBool, e ->
        let const_e = (const_fold_simple e env) in
        begin match const_e with
          | Bool(b) -> Bool(true)
          | Num(n) -> Bool(false)
          | _ -> sexp
        end
      | _ -> Prim1(op, (const_fold_simple exp env))
    end
  | Prim2(op, left, right) ->
    let const_left = (const_fold_simple left env) in
    let const_right = (const_fold_simple right env) in
    begin match const_left, const_right with
      | Num(n1), Num(n2) ->
        begin match op with
          | Plus ->
            begin match (n1, n2) with
              | (0, n) -> Num(n)
              | (n, 0) -> Num(n)
              | _ -> Num(n1 + n2)
            end
          | Minus ->
            begin match (n1, n2) with
              | (n, 0) -> Num(n)
              | (0, n) -> Num(~-n)
              | _ -> Num(n1 - n2)
            end
          | Times ->
            begin match (n1, n2) with
              | (0, n) -> Num(0)
              | (n, 0) -> Num(0)
              | _ -> Num(n1 * n2)
            end
          | Less -> Bool(n1 < n2)
          | Greater -> Bool(n1 > n2)
          | LessEq -> Bool(n1 <= n2)
          | GreaterEq -> Bool(n1 >= n2)
          | Eq -> Bool(n1 == n2)
          | _ -> failwith "Operation not for numbers"
        end
      | Bool(n1), Bool(n2) ->
        begin match op with
          | And -> Bool(n1 && n2)
          | Or -> Bool(n1 || n2)
          | _ -> failwith "Operation not for booleans"
        end
      | _ -> Prim2(op, const_left, const_right)
    end
  | App(fn, args) ->
    App(fn, (List.map
               (fun (a) ->
                  begin  match a with
                  | Id(name) ->
                    if (List.mem_assoc name env)
                    then
                      let s = (List.assoc name env) in
                      begin match s with
                      | App(fn, args) -> Id(name)
                      | _ -> (const_fold_simple a env)
                      end
                    else (const_fold_simple a env)
                  | _ -> (const_fold_simple a env)
                  end)
               args))
;;


let rec print_assoc_env (env : (simple_expr * simple_expr) list) : string =
  match env with
  | [] -> ""
  | (key, v)::rest ->
    "Key: " ^ (string_of_simple key) ^ " ; " ^ "value: " ^ (string_of_simple v) ^ "\n" ^ (print_assoc_env rest)

let rec cse (prog : tag aprogram) : unit aprogram =
  let purity = purity_env prog in
  (* This table maps arbitrary simple expressions to simpler ones
     that are equal to them: for example, "let x = a + b in" should map (a + b)
     to x.  You will likely need the generality of simple_expr for both the
     keys and the values of this table, but if you're careful, you might
     be able to simplify it to map simpl_exprs to strings. *)
  let equiv_exprs : (simple_expr * simple_expr) list = [] in
  match prog with
  | AProgram(dstructs, prog_body, _) ->
    AProgram((List.map untag_dstruct dstructs), (cse_a prog_body equiv_exprs purity), ())
and cse_a (aexp : 'a aexpr) (assoc_env : (simple_expr * simple_expr) list) (purity : (string * bool) list): unit aexpr =
  match aexp with
  | ALet(name, binding, body, _) ->
    let csed_binding = (cse_c binding assoc_env purity) in
    let new_assoc_env = (make_new_assoc_env name binding assoc_env purity) in
    ALet(name, csed_binding, (cse_a body new_assoc_env purity), ())
  | ACExpr(c) ->
    ACExpr(cse_c c assoc_env purity)
  | ASeq(cex, aex, _) -> ASeq((cse_c cex assoc_env purity), (cse_a aex assoc_env purity), ())
  | ALetRec(bindings, body, _) ->
    let csed_bindings = List.map (fun (n, b) -> (n, (cse_c b assoc_env purity))) bindings in
    let rec new_assoc_env_lr binds env =
      match binds with
      | [] -> env
      | (name, bind)::rest -> (new_assoc_env_lr rest (make_new_assoc_env name bind env purity)) in
    let new_assoc_env = new_assoc_env_lr bindings assoc_env in
    ALetRec(csed_bindings, (cse_a body new_assoc_env purity), ())
and make_new_assoc_env (name : string) (cexp : 'a cexpr) (assoc_env : (simple_expr * simple_expr) list) (purity : (string * bool) list) : (simple_expr * simple_expr) list =
  let simple = cexpr_to_simple_opt cexp in
  match simple with
  | Some s ->
    let simplified_binding = (cse_simple s assoc_env purity) in
    begin match simplified_binding with
      | Id(b) -> ((Id(name), simplified_binding)::assoc_env)
      | _ -> (((cse_simple s assoc_env purity), Id(name))::assoc_env)
    end
  | None -> assoc_env
and cse_c (cexp : 'a cexpr) (assoc_env : (simple_expr * simple_expr) list) (purity : (string * bool) list) : unit cexpr =
  let simple = cexpr_to_simple_opt cexp in
  match simple with
  | Some s -> (simple_to_cexpr (cse_simple s assoc_env purity))
  | None -> (cse_not_simple cexp assoc_env purity)
and cse_immexpr (imm : 'a immexpr) (assoc_env : (simple_expr * simple_expr) list) (purity : (string * bool) list): unit immexpr =
  let csed_cexp = (cse_c (CImmExpr(imm)) assoc_env purity) in
  match csed_cexp with
    | CImmExpr(something) -> something
    | _ -> failwith "Impossible"
and cse_not_simple (cexp : 'a cexpr) (assoc_env : (simple_expr * simple_expr) list) (purity : (string * bool) list) : unit cexpr =
  match cexp with
  | CIf(cond, thn, els, _) ->
    let cond_simp_c = (cse_immexpr cond assoc_env purity) in
    let thn_simp = (cse_a thn assoc_env purity) in
    let els_simp = (cse_a els assoc_env purity) in
    (CIf(cond_simp_c, thn_simp, els_simp, ()))
  | CTuple(vals_list, _) ->
    let new_vals_live_ids =
      (List.map
         (fun (a) -> (cse_c (CImmExpr(a)) assoc_env purity))
         vals_list) in
    (CTuple((List.map untag_immexpr vals_list), ()))
  | CGetItem(tup, idx, _) ->
    let tup_simp_c = (cse_immexpr tup assoc_env purity) in
    let idx_simp_c = (cse_immexpr idx assoc_env purity) in
    (CGetItem(tup_simp_c, idx_simp_c, ()))
  | CSetItem(tup, idx, new_val, _) ->
    let tup_simp_c = (cse_immexpr tup assoc_env purity) in
    let idx_simp_c = (cse_immexpr idx assoc_env purity) in
    let new_val_simp_c = (cse_immexpr new_val assoc_env purity) in
    (CSetItem(tup_simp_c, idx_simp_c, new_val_simp_c, ()))
  | CLambda(names, body, _) ->
    let body_simp = (cse_a body assoc_env purity) in
    (CLambda(names, body_simp, ()))
  | _ -> failwith "Not complex"
and cse_simple (sexp : simple_expr) (assoc_env : (simple_expr * simple_expr) list) (purity : (string * bool) list) : simple_expr =
  match sexp with
  | Id(name) ->
    if (List.mem_assoc sexp assoc_env)
    then List.assoc sexp assoc_env
    else sexp
  | Num(n) -> sexp
  | Bool(b) -> sexp
  | Prim1(op, exp) ->
    let cse_prim1 = (Prim1(op, (cse_simple exp assoc_env purity))) in
    if (List.mem_assoc cse_prim1 assoc_env)
    then List.assoc cse_prim1 assoc_env
    else cse_prim1
  | Prim2(op, left, right) ->
    let cse_prim2 = (Prim2(op, (cse_simple left assoc_env purity), (cse_simple right assoc_env purity))) in
    if (List.mem_assoc cse_prim2 assoc_env)
    then List.assoc cse_prim2 assoc_env
    else cse_prim2
  | App(fn, args) ->
    begin match fn with
      | Id(name) ->
        let args_sexps = List.map (fun (a) -> (cse_simple a assoc_env purity)) args in
        let cse_app = (App((cse_simple fn assoc_env purity), args_sexps)) in
        if ((List.mem_assoc cse_app assoc_env) && (List.assoc (name ^ "_body") purity)) (* lambda body is pure, so you can use CSE *)
        then List.assoc cse_app assoc_env
        else cse_app
      | _ -> failwith "Impossible"
    end
;;


let rec dae (prog : tag aprogram) : unit aprogram =
  let purity = purity_env prog in
    match prog with
      | AProgram(dstructs, prog_body, _) ->
        let (new_prog, live_ids) = dae_a prog_body [] purity in
        AProgram((List.map untag_dstruct dstructs), new_prog, ())
and dae_a (aexp : 'a aexpr) (live_ids : string list) (purity : (string * bool) list) : (unit aexpr * string list)  =
  match aexp with
  | ALet(name, binding, body, _) ->
    let (new_body, new_body_live_ids) = dae_a body live_ids purity in
    if (List.assoc name purity)
    (* name is pure, do DAE on binding and body *)
    then
      if List.mem name new_body_live_ids
      then
        let (new_bind, new_bind_live_ids) = dae_c binding live_ids purity in
        (ALet(name, new_bind, new_body, ()), new_bind_live_ids @ new_body_live_ids @ live_ids)
      else (new_body, new_body_live_ids @ live_ids)
      (* name is impure, only do DAE on body -- you must keep this let binding *)
    else
      let (new_bind, new_bind_live_ids) = dae_c binding live_ids purity in
      if List.mem name new_body_live_ids
      then (ALet(name, new_bind, new_body, ()), new_bind_live_ids @ new_body_live_ids @ live_ids)
      else (ASeq(new_bind, new_body, ()), new_bind_live_ids @ new_body_live_ids @ live_ids)
  | ACExpr(c) ->
    let (new_c, new_live_ids) = (dae_c c live_ids purity) in
    (ACExpr(new_c), new_live_ids @ live_ids)
  | ASeq(cex, aex, _) ->
    let (new_c, new_c_live_ids) = (dae_c cex live_ids purity) in
    let (new_a, new_a_live_ids) = (dae_a aex live_ids purity) in
    (ASeq(new_c, new_a, ()), (new_c_live_ids @ new_a_live_ids @ live_ids))
  | ALetRec(bindings, body, _) ->
    let binds_c = List.map (fun (name, c) -> let (new_c, ids) = (dae_c c live_ids purity) in (name, new_c)) bindings in
    let binds_live_ids =
      List.flatten (List.map (fun (name, c) -> let (new_c, ids) = (dae_c c live_ids purity) in ids) bindings) in
    let (body_a, body_ids) = (dae_a body binds_live_ids purity) in
    (ALetRec(binds_c, body_a, ()), (body_ids @ binds_live_ids @ live_ids))
  | _ -> failwith "NYI"
and dae_c (cexp : 'a cexpr) (live_ids : string list) (purity : (string * bool) list): (unit cexpr * string list) =
  let simple = cexpr_to_simple_opt cexp in
  match simple with
  | Some s ->
    let (new_simp, simp_live_ids) = (dae_simple s live_ids) in
    ((simple_to_cexpr new_simp), simp_live_ids)
  | None -> (dae_not_simple cexp live_ids purity)
and dae_not_simple (cexp : 'a cexpr) (live_ids : string list) (purity : (string * bool) list) : (unit cexpr * string list) =
  match cexp with
  | CIf(cond, thn, els, _) ->
    let (cond_simp_c, cond_ids) = (dae_c (CImmExpr(cond)) live_ids purity) in
    let (thn_simp, thn_ids) = (dae_a thn live_ids purity) in
    let (els_simp, els_ids) = (dae_a els live_ids purity) in
    (CIf((untag_immexpr cond), thn_simp, els_simp, ()), (cond_ids @ thn_ids @ els_ids @ live_ids))
  | CTuple(vals_list, _) ->
    let new_vals_live_ids =
      List.flatten
        (List.map
           (fun (a) -> let (c, ids) = (dae_c (CImmExpr(a)) live_ids purity) in ids)
           vals_list) in
    (CTuple((List.map untag_immexpr vals_list), ()), new_vals_live_ids @ live_ids)
  | CGetItem(tup, idx, _) ->
    let (tup_simp_c, tup_ids) = (dae_c (CImmExpr(tup)) live_ids purity) in
    let (idx_simp_c, idx_ids) = (dae_c (CImmExpr(idx)) live_ids purity) in
    (CGetItem((untag_immexpr tup), (untag_immexpr idx), ()), tup_ids @ idx_ids @ live_ids)
  | CSetItem(tup, idx, new_val, _) ->
    let (tup_simp_c, tup_ids) = (dae_c (CImmExpr(tup)) live_ids purity) in
    let (idx_simp_c, idx_ids) = (dae_c (CImmExpr(idx)) live_ids purity) in
    let (new_val_simp_c, val_ids) = (dae_c (CImmExpr(new_val)) live_ids purity) in
    (CSetItem((untag_immexpr tup), (untag_immexpr idx), (untag_immexpr new_val), ()),
     tup_ids @ idx_ids @ val_ids @ live_ids)
  | CLambda(names, body, _) ->
    let (body_simp, body_ids) = (dae_a body live_ids purity) in
    (CLambda(names, body_simp, ()), (body_ids @ live_ids))
  | _ -> failwith "Not complex"
and dae_simple (sexp : simple_expr) (live_ids : string list) : (simple_expr * string list) =
  match sexp with
  | Id(name) -> (sexp, (name::live_ids))
  | Num(n) -> (sexp, live_ids)
  | Bool(b) -> (sexp, live_ids)
  | Prim1(op, exp) ->
    let (exp_sexp, new_live_ids) = dae_simple exp live_ids in
    (Prim1(op, exp_sexp), new_live_ids @ live_ids)
  | Prim2(op, left, right) ->
    let (left_sexp, new_left_live_ids) = dae_simple left live_ids in
    let (right_sexp, new_right_live_ids) = dae_simple right live_ids in
    (Prim2(op, left_sexp, right_sexp), new_right_live_ids @ new_left_live_ids @ live_ids)
  | App(fn, args) ->
    let (fn_sexp, new_fn_live_ids) = dae_simple fn live_ids in
    let args_sexps = List.map (fun (a) -> let (s, ids) = (dae_simple a live_ids) in s) args in
    let new_args_live_ids =
      List.flatten (List.map (fun (a) -> let (s, ids) = (dae_simple a live_ids) in ids) args) in
    (App(fn_sexp, args_sexps), new_fn_live_ids @ new_args_live_ids @ live_ids)
;;
