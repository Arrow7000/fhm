let rec f (x : 'T) : 'T =
    if true then x
    else
        ignore (f 0)
        ignore (f true)
        x
