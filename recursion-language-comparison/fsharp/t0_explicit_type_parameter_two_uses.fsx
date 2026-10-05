let rec f<'T> (x : 'T) : 'T =
    if true then x
    else
        ignore (f 0)
        ignore (f true)
        x

let result = (f 0, f true)
