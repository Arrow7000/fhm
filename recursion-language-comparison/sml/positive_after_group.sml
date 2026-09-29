fun id x =
  if true then x else id x

val result = (id 0, id true)
