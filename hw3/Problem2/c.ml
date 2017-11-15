type aexp = 
  | CONST of int 
  | VAR of var
  | ADD of aexp * aexp 
  | MUL of aexp * aexp 
  | SUB of aexp * aexp
  
and bexp = 
  | TRUE 
  | FALSE 
  | EQ of aexp * aexp 
  | LT of aexp * aexp 
  | NOT of bexp 
  | AND of bexp * bexp

and stmt =
  | ASSIGN of var * aexp 
  | SKIP
  | SEQ of stmt * stmt
  | IF of bexp * stmt * stmt
  | WHILE of bexp * stmt
  | BLOCK of var * aexp * stmt
  | READ of var
  | PRINT of aexp 
and var = string
type program = stmt

type value = Int of int
type loc = Loc of int 
type env = (var * loc) list
type mem = (loc * value) list

(* environment *)
let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec apply_env e x = 
  match e with
  | [] -> raise (Failure (x ^ " is unbound in Env"))
  | (y,v)::tl -> if x = y then v else apply_env tl x

(* memory *)
let empty_mem = [] 
let extend_mem (l,v) m = (l,v)::m
let rec apply_mem m l = 
  match m with
  | [] -> raise (Failure ("Location " ^ string_of_int ((fun (Loc n) -> n) l) ^ " is unbound in Mem"))
  | (y,v)::tl -> if l = y then v else apply_mem tl l

let counter = ref 0
let new_location () = counter:=!counter+1; Loc (!counter)

exception NotImplemented

let rec eval_aexp : aexp -> env -> mem -> int
=fun a env mem ->
	let arith x y exp =
		let a = eval_aexp x env mem in
		let b = eval_aexp y env mem in
		match exp with
		| ADD (_,_) -> (a+b)
		| SUB (_,_) -> (a-b)
		| MUL (_,_) -> (a*b)
		| _ -> raise @@ Failure "Arithmetic error occured."
	in
	match a with
	| CONST n -> n
	| VAR x -> 
		(fun i -> match i with Int j -> j) @@ apply_mem mem @@ apply_env env x
	| ADD (a1,a2) -> arith a1 a2 a
	| SUB (a1,a2) -> arith a1 a2 a
	| MUL (a1,a2) -> arith a1 a2 a

and eval_bexp : bexp -> env -> mem -> bool
=fun b env mem ->
	match b with
	| TRUE -> true
	| FALSE -> false
	| EQ (a1,a2) -> 
		eval_aexp a1 env mem = eval_aexp a2 env mem
	| LT (a1,a2) ->
		eval_aexp a1 env mem <= eval_aexp a2 env mem
	| NOT b -> not(eval_bexp b env mem)
	| AND (b1,b2) ->
		eval_bexp b1 env mem && eval_bexp b2 env mem
	

let rec eval : stmt -> env -> mem -> mem
=fun s env mem -> 
	match s with
	| ASSIGN (v,a) ->
		let loca = apply_env env v in
		extend_mem (loca,Int(eval_aexp a env mem)) mem
	| SKIP -> mem
	| SEQ (s1,s2) ->
		let m' = eval s1 env mem in
		eval s2 env m' 
	| IF (b,s1,s2) ->
	begin
		let b = eval_bexp b env mem in
		match b with
		| true -> eval s1 env mem
		| false -> eval s2 env mem
	end
	| WHILE (b,s) ->
	begin
		match eval_bexp b env mem with
		| true -> 
			let m' = eval s env mem in
			eval (WHILE(b,s)) env m'
		| false -> mem
	end
	| BLOCK (v,a,s) ->
		let loca = new_location () in
		let newmem = extend_mem (loca,Int(eval_aexp a env mem)) mem in
		let newenv = extend_env (v,loca) env in
		eval s newenv newmem
	| READ x -> extend_mem (apply_env env x, Int (read_int())) mem (* Do not modify *)
	| PRINT e -> print_int (eval_aexp e env mem); print_newline(); mem (* Do not modify *)

let execute : program -> unit 
=fun pgm -> ignore (eval pgm empty_env empty_mem)
