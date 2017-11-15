/* read n and print n! */
begin var x:=0;
  begin var y:=1; 
    read(x);
    while (!(x=1)) {
      y := y * x;
      x := x - 1
    };
  print(y)
  end
end
