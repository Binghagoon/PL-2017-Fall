let smallest_divisor a =	
	let rec f a b =
		if a < b*b then a
		else if a mod b == 0 then b
		else f a (b+1)
		in f a 2
