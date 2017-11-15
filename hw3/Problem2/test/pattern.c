begin var x := 0;
  begin var i:= 1;
    begin var r := 0;
      read(x);
        while(i<=x){
	  r := r*10;
	  r := r+i;
	  print(r);
	  i := i+1
	};
    end
  end
end

