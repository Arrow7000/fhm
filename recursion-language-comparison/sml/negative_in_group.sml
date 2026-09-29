fun 'a f (x : 'a) : 'a =
  if true then x
  else
    let
      val _ = f 0
      val _ = f true
    in
      x
    end
