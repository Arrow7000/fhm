let rec ping<'a> (n: int) (x: 'a) : int =
    if n < 1 then 0 else 1 + pong (n-1) [x]
and pong<'b> (n: int) (y: 'b) : int =
    if n < 1 then 0 else 1 + ping (n-1) (y, y)
printfn "%A" (ping 4 true, pong 4 'c')
