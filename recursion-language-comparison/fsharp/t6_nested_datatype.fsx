type Nested<'a> = Flat of 'a | Nest of Nested<'a list>
let rec depth<'a> (t: Nested<'a>) : int =
    match t with
    | Flat _ -> 0
    | Nest n -> 1 + depth n
printfn "%d" (depth (Nest (Nest (Flat [[1;2]]))))
