let rec f<'a> (x: 'a) : 'a = if true then x else (let _ = useF 0 in x)
and useF _ = (f 1, f true)
printfn "%A" (useF 0)
