begin var x := 2;
  begin var y := 1;
    while (!(x=1)) {
      y := y * x;
      x := x - 1;
      while (y <= 10) {
        y := y + 1
      }
    };
    print(y)
  end
end
