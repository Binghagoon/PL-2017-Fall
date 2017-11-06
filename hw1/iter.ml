let rec iter a f =
	if a == 1 then f
	else fun x -> (iter (a-1) f) (f x)

