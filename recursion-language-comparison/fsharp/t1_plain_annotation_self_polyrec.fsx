let rec wrapN (n: int) (x: 'a) : int =
    if n < 1 then 0 else 1 + wrapN (n-1) [x]
printfn "%d" (wrapN 3 true)
