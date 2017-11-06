let rec fastexpt a e =
	if e == 1 then a else
	if e mod 2 == 0 then
		let b = fastexpt a (e/2) in b*b
	else
		let b = fastexpt a (e/2) in b*b*a
