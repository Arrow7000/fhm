let rec f : 'a. 'a -> 'a =
  fun x ->
    if true then x
    else begin
      ignore (f 0);
      ignore (f true);
      x
    end

let result = (f 0, f true)
