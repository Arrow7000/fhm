let rec bad n x = if n < 1 then 0 else bad (n-1) [x]
printfn "%d" (bad 3 true)
