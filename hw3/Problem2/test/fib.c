/* print fib(1) ... fib(30) */
begin var x := 0;
  begin var y := 1;
    begin var z := 0;
      begin var i := 0;
        begin var n := 0;
          begin var j := 1;
            while (j <= 30) {
              while (i <= j-1) {
                y := z + y;
                z := x;
                x := y;
                i := i + 1;
              };
              print (y);
              j := j+1
            }
          end
        end
      end
    end
  end
end
