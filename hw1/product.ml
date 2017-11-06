let rec product f u v =
	if u == v then f u
	else (f u) * product f (u+1) v
