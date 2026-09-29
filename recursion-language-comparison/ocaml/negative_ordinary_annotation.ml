let rec f (x : 'a) : 'a =
  if true then x
  else begin
    ignore (f 0);
    ignore (f true);
    x
  end
