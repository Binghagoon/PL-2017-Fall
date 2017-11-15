type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
  | NEWREF of exp 
  | DEREF of exp
  | SETREF of exp * exp
  | SEQ of exp * exp
  | BEGIN of exp
and var = string

type value = 
    Int of int 
  | Bool of bool 
  | Closure of var * exp * env 
  | RecClosure of var * var * exp * env
  | Loc of loc
and loc = int
and env = (var * value) list
and mem = (loc * value) list

(* conversion of value to string *)
let value2str v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Loc l -> "Loc "^(string_of_int l)
  | Closure (x,e,env) -> "Closure "
  | RecClosure (f,x,e,env) -> "RecClosure "^f

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
  | [] -> raise (Failure ("Location " ^ string_of_int l ^ " is unbound in Mem"))
  | (y,v)::tl -> if l = y then v else apply_mem tl l

(* use the function 'new_location' to generate a fresh memory location *)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

(*****************************************************************)
(* TODO: Implement the eval function. Modify this function only. *)
(*****************************************************************)
let rec eval : exp -> env -> mem -> value * mem
=fun exp env mem -> 
	let parseint v =
		match v with
		| Int i -> i
		| _ -> raise UndefinedSemantics
	in
	let arith e1 e2 bop env mem =
		let (v1,m1) = eval e1 env mem in
		let (v2,m2) = eval e2 env m1 in
		let i1 = parseint v1 in
		let i2 = parseint v2 in
		(Int (bop i1 i2), m2)
	in	
	match exp with
	| CONST n -> (Int n,mem)
	| VAR x -> (apply_env env x,mem)
	| ADD (e1,e2) -> arith e1 e2 (+) env mem
	| SUB (e1,e2) -> arith e1 e2 (-) env mem
	| MUL (e1,e2) -> arith e1 e2 ( * ) env mem
	| DIV (e1,e2) -> arith e1 e2 (/) env mem
	| ISZERO e ->
	begin
		let (v,m) = eval e env mem in
		match v with
		| Int i -> if i=0 then (Bool true,m) else (Bool false,m)
		| _ -> raise UndefinedSemantics
	end
	| READ -> (Int (read_int()),mem)
	| IF (e1,e2,e3) ->
	begin
		let (v,m) = eval e1 env mem in
		match v with
		| Bool true -> eval e2 env mem
		| Bool false -> eval e3 env mem
		| _ -> raise UndefinedSemantics
	end
	| LET (v,e1,e2) -> 
		let (v1,m1) = eval e1 env mem in
		let newenv = extend_env (v,v1) env in
		eval e2 newenv m1
	| LETREC (v1,v2,e1,e2) -> 
		let newenv = extend_env (v1,RecClosure (v1,v2,e1,env)) env in
		eval e2 newenv mem
	| PROC (v,e) -> 
		(Closure (v,e,env),mem)
	| CALL (e1,e2) -> begin
		match eval e1 env mem with
		| (Closure (x,e,newenv),m1) -> begin
			let (v,newmem) = eval e2 env mem in
			let newenv = extend_env (x,v) newenv in
			eval e newenv newmem
		end
		| (RecClosure (f,x1,e',env'),m1) -> begin
			let (x,m2) = eval e2 env m1 in
			let newenv = extend_env (x1,x) env' in
			let newenv = extend_env (f,RecClosure(f,x1,e',env')) newenv in
			eval e' newenv m2
		end
		| _ -> raise UndefinedSemantics
	end
	| NEWREF e -> 
		let (v,m1) = eval e env mem in
		let loc = new_location () in
		(Loc loc,extend_mem (loc,v) m1)
	| DEREF e -> begin
		let (l,m1) = eval e env mem in
		match l with
		| Loc l ->
			let dat = apply_mem m1 l in
			(dat,m1)
		| _ -> raise UndefinedSemantics
	end
	| SETREF (e1,e2) -> begin
		let (l,m1) = eval e1 env mem in
		let (v,m2) = eval e2 env m1 in
		match l with
		| Loc l -> (v,extend_mem (l,v) m2)
		| _ -> raise UndefinedSemantics
	end
	| SEQ (e1,e2) -> 
		let (v1,m1) = eval e1 env mem in
		eval e2 env m1
	| BEGIN e -> 
		eval e env mem


(* driver code *)
let run : program -> value
=fun pgm -> (fun (v,_) -> v) (eval pgm empty_env empty_mem) 
