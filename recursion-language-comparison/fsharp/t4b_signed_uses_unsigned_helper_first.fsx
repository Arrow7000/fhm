let rec helper x = if true then x else (let _ = consumer 0 in x)
and consumer (n: int) : int * bool = (helper n, helper true)
printfn "%A" (consumer 5)
