let rec f<'a> (x: 'a) : 'a = if true then x else (let _ = g 0 in x)
and g n = (h 1, h true)
and h x = if true then x else (let _ = f 0 in x)
printfn "%A %c" (g 0) (f 'c')
