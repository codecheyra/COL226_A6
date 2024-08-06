(* Execution function for the SECD machine, implementing call-by-value semantics for an extended lambda calculus language. *)

type expr = 
  | Var of string
  | Abs of string * expr
  | App of expr * expr
  | Num of int
  | Bool of bool
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | If of expr * expr * expr
  | Tuple of expr list
  | Lt of expr * expr
  | Gt of expr * expr
  | Eq of expr * expr
  | Leq of expr * expr
  | Geq of expr * expr
  | Neq of expr * expr
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  
  | Proj of expr * int;;


type opcode = 
  | PUSH_INT of int
  | PUSH_BOOL of bool
  | LOOKUP of string
  | MKCLOS of string * opcode list
  (* | CLOSURE of string * expr * opcode list *)
  | APP
  | RET
  | ADD
  | SUB
  | MUL
  | IF of opcode list * opcode list
  | TUPLE of opcode list list
  | LT
  | GT
  | EQ
  | LEQ
  | GEQ
  | NEQ
  | AND
  | OR
  | NOT
  | PROJ of int
  | PACK of int
  | UNPACK of int;;
  (* doubt in pack and unpack here *)

(* initial machine state, doubt in which file or where to write, let it be here for a while *)

type value =
  | VNum of int
  | VBool of bool
  | VClosure of string * opcode list * (string*value) list
  | VTuple of value list

type  environment = (string * value) list
type state = {
  stack : value list;
  env : environment;
  code : opcode list;
  dump : (value list * environment * opcode list) list;
};;


(* Compiler for an extended lambda calculus language to opcodes for SECD machine execution. *)



(* Function to compile expressions into a list of opcodes *)

let rec compile expr = 
  match expr with
  | Var x -> [LOOKUP x]
  (* | MKCLOS (x, e) -> [MKCLOS (x, compile e) @ [RET]] *)
  | Abs (x, e) -> [MKCLOS (x, compile e)]
  | App (e1, e2) -> (compile e1) @ (compile e2) @ [APP]
  | Num n -> [PUSH_INT(n)]
  | Bool b -> [PUSH_BOOL(b)]
  | Add (e1, e2) -> (compile e1) @ (compile e2) @ [ADD]
  | Sub (e1, e2) -> (compile e1) @ (compile e2) @ [SUB]
  | Mul (e1, e2) -> (compile e1) @ (compile e2) @ [MUL]
  | If (e1, e2, e3) -> (compile e1) @ [IF (compile e2, compile e3)]
  (* | Tuple es -> List.concat (List.map compile es) @ [TUPLE (List.length es)] *)
  | Tuple es ->
    let compiled_elements = List.map compile es in  (* Compile each element of the tuple *)
    [TUPLE compiled_elements]  (* Use the compiled elements directly *)
  | Lt (e1, e2) -> (compile e1) @ (compile e2) @ [LT]
  | Eq (e1, e2) -> (compile e1) @ (compile e2) @ [EQ]
  | Gt (e1, e2) -> (compile e1) @ (compile e2) @ [GT]
  | Leq (e1, e2) -> (compile e1) @ (compile e2) @ [LEQ]
  | Geq (e1, e2) -> (compile e1) @ (compile e2) @ [GEQ]
  | Neq (e1, e2) -> (compile e1) @ (compile e2) @ [NEQ]
  | And (e1, e2) -> (compile e1) @ (compile e2) @ [AND]
  | Or (e1, e2) -> (compile e1) @ (compile e2) @ [OR]
  | Not e -> (compile e) @ [NOT]
  | Proj (e, n) -> (compile e) @ [PROJ n]


  (* once check Abs and MKCLOS *)

(* Extracts a value from a VNum or VBool, raises error if the value is of another type. *)

let extract_num = function
  | VNum n -> [PUSH_INT(n)]
  | _ -> failwith "Expected a number"

let extract_bool = function
  | VBool b -> [PUSH_BOOL(b)]
  | _ -> failwith "Expected a boolean"

(* Evaluates a binary operation on two numerical values on top of the stack. *)
let eval_bin_op op stack = 
  match stack with
  | VNum v1 :: VNum v2 :: stack' -> VNum (op v2 v1) :: stack'
  | _ -> failwith "Expected two numbers on the stack for binary operation"

(* Evaluates a binary operation on two boolean values on top of the stack. *)
let eval_bin_bool op stack = 
  match stack with
  | VBool b1 :: VBool b2 :: stack' -> VBool (op b2 b1) :: stack'
  | _ -> failwith "Expected two booleans on the stack for binary operation"

(* Main execution loop of the SECD machine. *)
let rec execute state = 
  match state with
  | { stack; env; code = []; dump = [] } ->
    begin match stack with
    | [result] -> result
    | _ -> failwith "Invalid finall state: Expected a single value on the stack"
    end
  | { stack; env; code = []; dump = (stack', env', c) :: dump' } ->
    execute { stack = (List.hd stack) :: stack'; env = env'; code = c; dump = dump' }
  | { stack; env; code; dump } -> 
    match code with 
    | PUSH_INT v :: c -> execute { stack =VNum v :: stack; env; code = c; dump }
    | PUSH_BOOL v :: c -> execute { stack = VBool v :: stack; env; code = c; dump }
    | LOOKUP x :: c -> 
      let v = List.assoc x env in
      execute { stack = v :: stack; env; code = c; dump }
    | MKCLOS (x, c1) :: c ->
      let closure = VClosure (x, c1, env) in
      execute { stack = closure :: stack; env; code = c; dump }
    | APP :: c ->
      begin match stack with
      | v :: VClosure (x, c1, closure_env) :: stack' ->
        execute { stack = []; env = (x,v) :: closure_env; code = c1; dump = (stack', env, c) :: dump }
      | _ -> failwith "Expected a closure on top of the stack for application, APP operation failed: Invalid stack configuration"
      end
    | RET :: c ->
      begin match dump with
      | (stack', env', newcode) :: dump' ->
        execute { stack = (List.hd stack) :: stack'; env = env'; code = newcode; dump = dump' }
      | _ -> failwith "RET operation failed: Invalid dump configuration or dump is empty"
      end
    | ADD :: c -> 
      let newstack = eval_bin_op (+) stack in
      execute { stack = newstack; env; code = c; dump }
    | SUB :: c ->
      let newstack = eval_bin_op (-) stack in
      execute { stack = newstack; env; code = c; dump }
    | MUL :: c ->
      let newstack = eval_bin_op ( * ) stack in
      execute { stack = newstack; env; code = c; dump }
    | IF (c1, c2) :: c ->
      begin match stack with
      | VBool true :: stack' -> execute { stack = stack'; env; code = c1 @ c; dump }
      | VBool false :: stack' -> execute { stack = stack'; env; code = c2 @ c; dump }
      | _ -> failwith "Top of the stack is not boolean"
      end
    | LT :: c ->
      let newstack = eval_bin_op (fun x y -> if x < y then 1 else 0) stack in
      execute { stack = newstack; env; code = c; dump }
    | GT :: c ->
      let newstack = eval_bin_op (fun x y -> if x > y then 1 else 0) stack in
      execute { stack = newstack; env; code = c; dump }
    | EQ :: c ->
      let newstack = eval_bin_op (fun x y -> if x = y then 1 else 0) stack in
      execute { stack = newstack; env; code = c; dump }
    | AND :: c ->
      let newstack = eval_bin_bool (&&) stack in
      execute { stack = newstack; env; code = c; dump }
    | OR :: c ->
      let newstack = eval_bin_bool (||) stack in
      execute { stack = newstack; env; code = c; dump }
    | NOT :: c ->
      begin match stack with
      | VBool b :: stack' -> execute { stack = VBool (not b) :: stack'; env; code = c; dump }
      | _ -> failwith "Expected a boolean on the stack for NOT operation"
      end
    | GEQ :: c ->
      let newstack = eval_bin_op (fun x y -> if x >= y then 1 else 0) stack in
      execute { stack = newstack; env; code = c; dump }
    | LEQ :: c ->
      let newstack = eval_bin_op (fun x y -> if x <= y then 1 else 0) stack in
      execute { stack = newstack; env; code = c; dump }
    | NEQ :: c ->
      let newstack = eval_bin_op (fun x y -> if x <> y then 1 else 0) stack in
      execute { stack = newstack; env; code = c; dump }
    | _ -> failwith "Invalid state: Code is empty"



































































    (* sir test case 1 *)
    (* secd [] [("x", VNum(1))] (compile (V "y")) [] ;; *)
    let test_expr = Var "x"
    let initial_state = {
      stack = [];
      env = [("y", VNum(1))];
      code = compile test_expr;
      dump = [];
    }
    
    (* Execute the test case *)
    let result = execute initial_state;;
    match result with
    | VNum n -> Printf.printf "Result: Num %d\n" n
    | VBool b -> Printf.printf "Result: Bool %b\n" b
    | _ -> Printf.printf "Result: Other\n"

    (* sir test case 2 *)
    (* secd [] [("x", VNum(1))] (compile (V "x")) [] ;; *)
    (* let test_expr2 = Var "x"
    let initial_state2 = {
      stack = [];
      env = [("x", VNum(1))];
      code = compile test_expr2;
      dump = [];
    }
    
    let result2 = execute initial_state2;;
    match result2 with
    | VNum n -> Printf.printf "Result: Num %d\n" n
    | VBool b -> Printf.printf "Result: Bool %b\n" b
    | _ -> Printf.printf "Result: Other\n" *)

    (* sir test case 3 *)
    (* secd [] [("x", VClos("x", [LOOKUP "y"; RET], [("y", VNum(2))])); ("y", VNum(1))] (compile (App(V "x", V "y"))) [] ;; *)
    (* let test_expr3 = App(Var "x", Var "y")
    let initial_state3 = {
      stack = [];
      env = [("x", VClosure("x", [LOOKUP "y"; RET], [("y", VNum(2))])); ("y", VNum(1))];
      code = compile test_expr3;
      dump = [];
    }
    let result3 = execute initial_state3;;
    match result3 with
    | VNum n -> Printf.printf "Result: Num %d\n" n
    | VBool b -> Printf.printf "Result: Bool %b\n" b
    | _ -> Printf.printf "Result: Other\n" *)

    (* sir test case 4 *)
    (* secd [] [("x", VNum(1))] (compile (App(Abs("x", V "x"), V "x"))) [] ;; *)
    (* let test_expr4 = App(Abs("x", Var "x"), Var "x")
    let initial_state4 = {
      stack = [];
      env = [("x", VNum(1))];
      code = compile test_expr4;
      dump = [];
    }
    let result4 = execute initial_state4;;
    match result4 with
    | VNum n -> Printf.printf "Result: Num %d\n" n
    | VBool b -> Printf.printf "Result: Bool %b\n" b
    | _ -> Printf.printf "Result: Other\n" *)

    (* sir testcase 5 *)
    (* secd [] [("x", VNum(1)); ("y", VNum(2))] (compile (App(Abs("y", V "y"), V "x"))) [] ;; *) (*- not coming man *)
    (* let test_expr5 = App(Abs("y", Var "y"), Var "x")
    let initial_state5 = {
      stack = [];
      env = [("x", VNum(1)); ("y", VNum(2))];
      code = compile test_expr5;
      dump = [];
    }
    let result5 = execute initial_state5;;
    match result5 with
    | VNum n -> Printf.printf "Result: Num %d\n" n
    | VBool b -> Printf.printf "Result: Bool %b\n" b
    | _ -> Printf.printf "Result: Other\n" *)

    (* sir testcase 6 *)
    (* secd [] [("x", VNum(1)); ("y", VNum(2))] (compile (App(Abs("y", Abs("x", V "y")), V "x"))) [] ;; *) (*- not working man*)
    (* let test_expr6 = App(Abs("y", Abs("x", Var "y")), Var "x")
    let initial_state6 = {
      stack = [];
      env = [("x", VNum(1)); ("y", VNum(2))];
      code = compile test_expr6;
      dump = [];
    }
    let result6 = execute initial_state6;;
    match result6 with
    | VNum n -> Printf.printf "Result: Num %d\n" n
    | VBool b -> Printf.printf "Result: Bool %b\n" b
    | _ -> Printf.printf "Result: Other\n" *)

    (* sir testcase 7 *)
    (* secd [] [("x", VNum(1)); ("y", VNum(2))] (compile (App(Abs("x", App(Abs("y", V "y"), V "x")), V "x"))) [] ;; *)
    (* let test_expr7 = App(Abs("x", App(Abs("y", Var "y"), Var "x")), Var "x")
    let initial_state7 = {
      stack = [];
      env = [("x", VNum(1)); ("y", VNum(2))];
      code = compile test_expr7;
      dump = [];
    }
    let result7 = execute initial_state7;;
    match result7 with
    | VNum n -> Printf.printf "Result: Num %d\n" n
    | VBool b -> Printf.printf "Result: Bool %b\n" b
    | _ -> Printf.printf "Result: Other\n" *)