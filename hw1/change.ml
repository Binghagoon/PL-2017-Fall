let rec change li amt =
	if amt == 0 then 1
	else if amt < 0 then 0
	else match li with
	| [] -> 0
	| hd::tl -> (change li (amt-hd)) + change tl amt
