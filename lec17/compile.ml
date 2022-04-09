(* compiler that allows incrementing & decrementing integers, vars, ifs and comparisons *)
(* also allows function definitions and applications *)

open Sexplib.Sexp
module Sexp = Sexplib.Sexp 
open Printf

(* 
  grammar: 
  expr : = <number> | (<op> <expr>) | <name> | (let (<name> <expr>) <expr>)
           | (if <expr> <expr> <expr>) | (<comp <expr> <expr>) | true | false 
           | (<name> <expr>)
  op := inc | dec 
  comp := < | > | = 
  def := (def (<name> <name> <name>) <expr>)
*)

(* type for env that maps variable names to stack offsets *)
type tenv = (string * int) list 

(* (inc (dec 4)) *)
type op = 
  | Inc 
  | Dec

(* could include <= and >= here *)
type comp = 
  | Less
  | Equal
  | Greater 

(* Eop is a tuple of the op and expression *)
type expr = 
  | ENum of int 
  | EBool of bool 
  | EOp of op * expr 
  (* use of a var *)
  | EId of string
  (* declaration of a var *)
  | ELet of string * expr * expr 
  (* if statement *)
  | EIf of expr * expr * expr 
  (* comp expression *)
  | EComp of comp * expr * expr
  (* function application *)
  | EApp of string * expr * expr  

(* for function definitions *)
(* functions now have two arguments *)
type def = DFun of string * string * string * expr

(* a program is a list of function defs followed by ONE expression *)
type prog = def list * expr 

(* counter to keep track of labels so we can generate fresh ones *)
(* this is a reference to a mutable integer that can be updated *)
let counter : int ref = ref 0;;

(* helper function for parsing base base *)
let int_of_string_opt (s: string) : int option = 
    try 
        (* if we can make the string into an int *)
        Some(int_of_string s)
    with 
        (* turn the failure into a None option *)
        Failure _ -> None      
;;

(* function to generate a string that represents a new label*)
let new_label (s: string) : string = 
        (* extract value of counter, increment it and update counter *)
        counter := (!counter) + 1;
        (* convert the counter value to a string *)
        let counter_string : string = string_of_int (!counter) in
        (* concatenate the root string and the counter string *)
        s ^ counter_string 
;;

(* helper for finding vars in env *)
let rec find (env: tenv) (x: string) : int option = 
    match env with 
    | [] -> None
    | (name, value) :: tl -> if x = name then Some(value) else find tl x 
;;     

(* helper for finding function defs in list of defs *)
let rec find_def (defs: def list) (fname: string) : def option = 
    match defs with 
    | [] -> None
    | (DFun(name, arg1, arg2, body)) :: rest -> if name = fname 
                                                then Some(DFun(name, arg1, arg2, body))
                                                else find_def rest fname
;; 

(* helper to calculate stack offsets on a 64 bit system *)
let stackloc (i: int) : int = i * 8;;

(* function to convert Sexpressions to expressions *)
(* .t is the type from the Sexp module *) 
let rec sexp_to_expr (se: Sexp.t) : expr = 
  match se with 
    (* base cases for booleans *)
    | Atom("true") -> EBool(true)
    | Atom("false") -> EBool(false) 
    (* convert the integer to a string *) 
    | Atom(s) -> (match int_of_string_opt s with 
                   | None -> EId(s)
                   | Some(i) -> ENum(i))
    (* match on whether it is an inc or a dec, then recurse *)
    (* arg could be another atom or a list *)
    | List([Atom("inc"); arg]) -> EOp(Inc, sexp_to_expr arg) 
    | List([Atom("dec"); arg]) -> EOp(Dec, sexp_to_expr arg)
    (* need to match further into the let to get access to the name of the var *)
    | List([Atom("let"); List([Atom(name); arg1]); arg2]) -> 
                    ELet(name, sexp_to_expr arg1, sexp_to_expr arg2 )
    | List([Atom("if"); se1; se2; se3]) -> 
                    EIf(sexp_to_expr se1, sexp_to_expr se2, sexp_to_expr se3) 
    (* comparison cases *)
    | List([Atom(">"); se1; se2]) -> EComp(Greater, sexp_to_expr se1, sexp_to_expr se2)
    | List([Atom("<"); se1; se2]) -> EComp(Less, sexp_to_expr se1, sexp_to_expr se2)
    | List([Atom("="); se1; se2]) -> EComp(Equal, sexp_to_expr se1, sexp_to_expr se2)
    (* any other string followed by an expression must be a function app *)
    | List([Atom(fname); arg1; arg2]) -> EApp(fname, sexp_to_expr arg1, sexp_to_expr arg2)  
    (* if it is not one of the above cases, not valid in our lang *)
    | _ -> failwith "Parse Expression Error"
;;

(* function to parse function definitions *)
let sexp_to_def (se: Sexp.t) : def = 
    match se with
    | List([Atom("def"); List([Atom(fname); Atom(argname1); Atom(argname2)]); body]) -> 
                     DFun(fname, argname1, argname2, sexp_to_expr body)
    | _ -> failwith "Parse Function Definition Error" 
;;

(* recursively parse an entire program *)
(* first handle each definition, then handle the expression *)
let rec parse_program (se: Sexp.t list) : prog = 
   match se with
   | [] -> failwith "Empty program" 
   | [e] -> ([], sexp_to_expr e)
   | def :: rest -> let defs, body = parse_program rest in 
                    ((sexp_to_def def) :: defs, body)  

;;

(* converts the AST into a list of instructions *)
(* added env argument which maps vars to their stack offset *)
(* stack index argument which tracks next available spot on the stack *)
(* defs argument which contains the list of function definitions *)
let rec expr_to_instrs (e: expr) (env: tenv) (si: int) (defs: def list): string list = 
    match e with 
    (* new base case for a boolean *) 
    | EBool(b) -> if b then ["mov rax, 1"] else ["mov rax, 0"]
    | ENum(i) -> (* base case -- result is in rax *)
                 [sprintf "mov rax, %d" i] 
    | EId(s) -> (* lookup in env *)
                (match find env s with 
                | None -> failwith "Unbound id"
                (* move from the appropriate stack offset to rax *)
                | Some(i) -> [sprintf "mov rax, [rsp - %d]" (stackloc i)])
    | EApp(fname, e1, e2) -> (* lookup fname in defs *) 
                       (match find_def defs fname with 
                       | None -> failwith "No such function definition"
                       | Some(DFun(name, arg1, arg2, body)) -> 
                           (* make aftercall label *)
                           let after : string = new_label "after" in 
                           (* move label to stack, need to save in register first *)
                           let move1 = [sprintf "mov rbx, %s" after] in
                           let move2  = [sprintf "mov [rsp-%d], rbx" (stackloc si)] in
                           (* save old rsp *)
                           let save_rsp = [sprintf "mov [rsp-%d], rsp" (stackloc (si + 1))] in
                           (* process first arg *)
                           let arg1_instrs  = expr_to_instrs e1 env (si + 2) defs in
                           (* save first arg *)
                           let savearg1 = [sprintf "mov [rsp-%d], rax" (stackloc (si + 2))] in
                           (* process arg2 *)
                           let arg2_instrs = expr_to_instrs e2 env (si + 3) defs in
                           (* save arg2 *)
                           let savearg2 = [sprintf "mov [rsp-%d], rax" (stackloc (si + 3))] in
                           (* reset rsp to point to aftercall label address *)
                           let reset_rsp = [sprintf "sub rsp, %d" (stackloc si)] in
                           (* jump to function *)
                           let jmp : string list = [sprintf "jmp %s" fname] in
                           (* set up after label *)
                           let after_label : string list = [sprintf "%s:" after] in
                           (* reset rsp *)
                           let rsp_back : string list = ["mov rsp, [rsp-16]"] in
                           move1 @ move2 @ save_rsp @ arg1_instrs @ 
                           savearg1 @ arg2_instrs @ savearg2 
                           @ reset_rsp @ jmp @ after_label @ rsp_back) 
    | EOp(op,e2) ->  eop_helper op e2 env si defs
    | EIf(c,i,el) -> if_helper c i el env si defs
    | EComp(c, e1, e2) -> comp_helper c e1 e2 env si defs 
    | ELet(x, v, b) -> (* generate instructions for what the value is bound to *)
                       (* result will be in rax *)
                       let (v_instrs : string list) = expr_to_instrs v env si defs in
                       (* move from rax to the 1st stack location *)
                       let (store: string list) = 
                           (* store the var into the next available spot on stack *)
                            [sprintf "mov [rsp-%d], rax" (stackloc si)] in
                       (* add the var and its stack offset to the env *)
                       (* generate instructions for the body of the let *)
                       let (b_instrs : string list) =
                               (* adding the var and its location to env *)
                               (* increment the stack index to not clobber future vars *) 
                               expr_to_instrs b ((x, si) :: env) (si + 1) defs in
                       (* append instructions together *)
                       v_instrs @ store @ b_instrs

(* helper function for the if *)
and if_helper (c: expr) (i: expr) (el:expr) (env: tenv) (si: int) (defs: def list) 
  : string list = 
    (* generate instructions for the condition expr *)
    let cond_instrs : string list = expr_to_instrs c env si defs in
    (* generate instructions for the if-block *)
    let if_instrs : string list = expr_to_instrs i env si defs in
    (* generate instructions for the else-block *)
    let else_instrs : string list = expr_to_instrs el env si defs in
    (* generate compare instruction *)
    let compare : string list  = ["cmp rax, 0"] in
    (* make a fresh else label *)
    let else_string : string = new_label "else" in
    (* make the actual else label that will go in the assembly *)
    let else_label: string list = [sprintf "%s:" else_string] in
    (* make the else jump *)
    let else_jmp : string list = [sprintf "je %s" else_string] in
    (* make a fresh after label *)
    let after_string : string = new_label "after" in
    (* make the actual else label that will go in the assembly *)
    let after_label : string list = [sprintf "%s:" after_string] in
    (* make the after jump *)
    let after_jmp : string list = [sprintf "jmp %s" after_string] in
    (* glue all of the instructions in the right order *)
    cond_instrs @ compare @ else_jmp @ if_instrs @ after_jmp @ else_label 
        @ else_instrs @ after_label 

(* helper for comparisons *)
and comp_helper (c: comp) (e1: expr) (e2: expr) (env: tenv) (si: int) (defs: def list) 
  : string list = 
    (* generate instructions for the first expression *)
    let e1_instrs : string list = expr_to_instrs e1 env si defs in 
    (* generate instructions for second expression, need to increment si to not clobber e1 *) 
    let e2_instrs : string list = expr_to_instrs e2 env (si + 1) defs in
    (* store result of first expression on stack *)
    let e1_store : string list = [sprintf "mov [rsp-%d], rax" (stackloc si)] in
    (* compare what's in rax to what was just stored on the stack *)
    let compare : string list = [sprintf "cmp [rsp-%d], rax"(stackloc si)] in 
    (* true returns 1 *)
    let true_instrs : string list  = ["mov rax, 1"] in
    (* false returns 0 *)
    let false_instrs : string list = ["mov rax, 0"] in
    (* set up false label so can jump to it *)
    let false_label : string =  new_label "false" in
    (* set up after label so can jump to it *) 
    let after_label : string = new_label "after" in 
    (* make unconditional jump so can jump after true instrs *)
    let ujmp : string list = [sprintf "jmp %s" after_label] in 
    (* smush together instrs up to compare *)
    let up_to_comp : string list = e1_instrs @ e1_store @ e2_instrs @ compare in
    (* smush together instrs after compare *)
    let after_comp : string list = true_instrs @ ujmp 
         @ [sprintf "%s:" false_label] @ false_instrs @ [sprintf "%s:" after_label] in
    (* need different jumps based on what comparison it is *)
    (match c with 
    | Equal -> (* jump to false when NOT EQUAL flag is set *)
               let jmp : string list = [sprintf "jne %s" false_label] in 
               (* smush everything together *)
               up_to_comp @ jmp @ after_comp                
    | Less ->  (* jump to false when GREATER EQUAL flag is set *)
               let jmp : string list = [sprintf "jge %s" false_label] in
               up_to_comp @ jmp @ after_comp
    | Greater -> (* jump to false when LESS EQUAL flag is set *)
               let jmp : string list = [sprintf "jle %s" false_label] in 
               up_to_comp @ jmp @ after_comp) 

(* helper function for unary operations, mutually recursive *) 
 and eop_helper (eop: op) (e: expr) (env: tenv) (si: int) (defs: def list) : string list = 
    let (rec_instrs : string list) = expr_to_instrs e env si defs in
    (* append the add or sub instruction to the recursive instructions *)
    (* the order of the append matters! *)
    (match eop with 
     | Inc -> rec_instrs @ ["add rax, 1"] 
     | Dec -> rec_instrs @ ["sub rax, 1"] ) 
;;

(* this is the callee code *)
let compile_def (d: def) (defs: def list) = 
   match d with 
   (* 4 b/c don't overwrite old rsp or args *)
   (* need to make sure we add arg to env so that function body can find it *)
   | DFun(fname, argname1, argname2, body) -> 
                   let body_instrs : string list = 
                           expr_to_instrs body [(argname1, 2); (argname2, 3)] 4 defs in
                 let fun_label : string list = [sprintf "%s:" fname] in
                     fun_label @ body_instrs @ ["ret"] 
;;

(* example original program: (inc (dec 3)) *)
(* program converted to AST: EOp(Inc,EOp(Dec,ENum(3))) *)
(* compiles a source program to an x86 string *)
(* source program is a list of Sexps *)
let compile (program: Sexp.t list) : string = 
  (* source program converted to function defs and expressions *)
  let defs, body = parse_program program in 
  (* compile each list definition and smush the lists of instrs into one list *)
  let (defs_instrs : string list) = 
          List.concat (List.map (fun d -> compile_def d defs) defs) in
  (* compile the expression *)
  (* initially env is empty and si is 1 to not clobber top of stack *)
  let (instrs: string list) = expr_to_instrs body [] 1 defs in
  (* add a newline to the generated instructions *)
  let (defs_str : string) = (String.concat "\n  " defs_instrs) in
  let (instrs_str: string) = (String.concat "\n  " instrs) in 
  (* add the boilerplate to instructions to make it work *)
  (* don't execute assembly for function defs until they are called from our code *)
  sprintf "
  section .text
  %s 
  global our_code_starts_here
  our_code_starts_here:
  %s
  ret\n" defs_str instrs_str;;

  (* top-level-function -- code execution starts here *) 
  let () = 
    (* opens the file passed in on the command line  *) 
    let input_file = (open_in (Sys.argv.(1))) in 
    (* reads the file in and converts it to a list of Sexps *) 
    let (input_program: Sexp.t list) = Sexp.input_sexps input_file in
    (* compiles the file to an X86 string *)  
    let (program: string) = compile input_program in 
    (* prints the resulting x86 string *) 
    printf "%s\n" program;;




