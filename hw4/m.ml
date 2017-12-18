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
and var = string

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ "\n")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty ->
	match e with
	| CONST _ ->
		[(ty,TyInt)]

	| VAR x -> begin
		try [(ty,TEnv.find tenv x)]
		with _ -> [(ty,TyVar x)] end

	| ADD (e1,e2) ->
		let eq1 = gen_equations tenv e1 TyInt in
		let eq2 = gen_equations tenv e2 TyInt in
		[(ty,TyInt)]@eq1@eq2

	| SUB (e1,e2) ->
		let eq1 = gen_equations tenv e1 TyInt in
		let eq2 = gen_equations tenv e2 TyInt in
		[(ty,TyInt)]@eq1@eq2

	| MUL (e1,e2) ->
		let eq1 = gen_equations tenv e1 TyInt in
		let eq2 = gen_equations tenv e2 TyInt in
		[(ty,TyInt)]@eq1@eq2

	| DIV (e1,e2) ->
		let eq1 = gen_equations tenv e1 TyInt in
		let eq2 = gen_equations tenv e2 TyInt in
		[(ty,TyInt)]@eq1@eq2

	| ISZERO e ->
		[(ty,TyBool)]@(gen_equations tenv e TyInt)

	| READ ->
		[(ty,TyInt)]

	| IF (e1,e2,e3) ->
		let eq1 = gen_equations tenv e1 TyBool in
		let eq2 = gen_equations tenv e2 ty in
		let eq3 = gen_equations tenv e3 ty in
		eq1@eq2@eq3

	| LET (x,e1,e2) ->
		let ty' = fresh_tyvar () in
		let tenv' = TEnv.extend (x,ty') tenv in
		let eq1 = gen_equations tenv e1 ty' in
		let eq2 = gen_equations tenv' e2 ty in
		eq1@eq2

	| LETREC (f,x,e1,e2) ->
		let tyx = fresh_tyvar () in
		let tye1 = fresh_tyvar () in
		let tyf = TyFun (tyx,tye1) in
		let tenvf = TEnv.extend (f,tyf) tenv in
		let tenvx = TEnv.extend (x,tyx) tenvf in
		let eq1 = gen_equations tenvx e1 tye1 in
		let eq2 = gen_equations tenvf e2 ty in
		eq1@eq2

	| PROC (x,e) ->
		let tyx = fresh_tyvar () in
		let ty' = fresh_tyvar () in
		let tenv' = TEnv.extend (x,tyx) tenv in
		[(ty,TyFun(tyx,ty'))]@(gen_equations tenv' e ty')

	| CALL (e1,e2) ->
		let ty' = fresh_tyvar () in
		let eq1 = gen_equations tenv e1 @@ TyFun(ty',ty) in
		let eq2 = gen_equations tenv e2 ty' in
		eq1@eq2

let solve : typ_eqn -> Subst.t
=fun eqns ->
	let rec metasub subst final =
		match subst with
		| [] -> []
		| (tyvar,ty)::tl ->
			if tyvar = final then (tyvar,ty)::(metasub tl final)
			else
				(tyvar,Subst.apply ty subst)::(metasub tl final)
	in

	let rec occucheck x tyb =			(* raise true if tyb has a type named x *)
		match tyb with
		| TyFun(a,b) -> occucheck x a || occucheck x b
		| TyVar y -> if x = y then true else false
		| _ -> false
	in

	let rec subsolve : typ_eqn -> Subst.t -> Subst.t
	= fun eqns subst ->
		match eqns with
		| [] -> subst
		| (tya,tyb)::tl ->
			let tya = Subst.apply tya subst in
			let tyb = Subst.apply tyb subst in
			if tya = tyb then subsolve tl subst  
			else
				match (tya,tyb) with
				| (TyVar x,_) ->
					if occucheck x tyb then raise TypeError
					else
					let subst' = Subst.extend x tyb subst in
					let subst' = metasub subst' x in			(*It sub. subst's element using tya = tyb *)
					subsolve tl subst'

				| (_,TyVar x) ->
					if occucheck x tya then raise TypeError
					else
					let subst' = Subst.extend x tya subst in
					let subst' = metasub subst' x in			(*It sub. subst's element using tya = tyb *)
					subsolve tl subst'

				| (TyFun(tyx,tyy),TyFun(tyz,tyw)) ->
					let neweqns = [(tyx,tyz);(tyy,tyw)]@tl in
					subsolve neweqns subst

				| (_,_) -> raise TypeError
	in

	let subst = subsolve eqns Subst.empty in
	metasub subst "NoneType"

(* typeof: Do not modify this function *)
let typeof : exp -> typ 
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns in
  try 
    let subst = solve eqns in
    let ty = Subst.apply new_tv subst in
     print_endline "= Substitution = ";
      Subst.print subst;
      print_endline "";
      print_endline ("Type of the given program: " ^ string_of_type ty);
      print_endline "";
      ty
  with TypeError -> (print_endline "The program does not have type. Rejected."); exit (1)
