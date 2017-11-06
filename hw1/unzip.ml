let unzip t =
	let rec append l a =
		match l with
		| [] -> [a]
		| hd::tl -> hd::(append tl a)
	in
		let rec tuz t x y =
			match t with
			| [] -> (x,y)
			| (a,b)::tl -> tuz tl (append x a) (append y b)
		in
			tuz t [] []
