let rec consumer (n: int) : int * bool = (helper n, helper true)
and helper x = if true then x else (let _ = consumer 0 in x)
printfn "%A" (consumer 5)
