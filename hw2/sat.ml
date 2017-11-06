type formula =
    True
  | False
  | Var of string
  | Neg of formula
  | And of formula * formula
  | Or of formula * formula
  | Imply of formula * formula
  | Iff of formula * formula


let sat : formula -> bool
= fun f ->
	let rec findenv f =
		match f with
		| Var s -> [s]
		| Neg a -> findenv a
		| And (a,b) -> List.append (findenv a) (findenv b)
		| Or (a,b) -> List.append (findenv a) (findenv b)
		| Imply (a,b) -> List.append (findenv a) (findenv b)
		| Iff (a,b) -> List.append (findenv a) (findenv b)
		| _ -> []
	in
	let env = findenv f in
	let rec matenv f al =
		match f with
		| True -> true
		| False -> false
		| Var s -> 
			let rec matdat al =
				match al with
				| [] -> false
				| hd::tl ->				
					 match hd with (a,b) -> if a=s then b else matdat tl
			in matdat al 
		| Neg a -> matenv a al
		| And (a,b) -> (matenv a al)&&(matenv b al)
		| Or (a,b) -> (matenv a al)||(matenv b al)
		| Imply (a,b) -> matenv (Or(Neg a, And(a,b))) al
		| Iff (a,b) -> matenv (Or(And(Neg a,Neg b), And(a,b))) al
	in
	let rec crtenv al =
		match al with
		| [] -> []
		| hd::tl -> let next = crtenv tl in List.append (
			List.map (fun x -> (hd,true)::x) next) (
			List.map (fun x -> (hd,false)::x) next)
	in
	let e = crtenv env in
	let rec inc al =
		match al with
		| [] -> matenv f [("",false)]
		| hd::tl -> (matenv f hd)||(inc tl)

	in
		inc e
