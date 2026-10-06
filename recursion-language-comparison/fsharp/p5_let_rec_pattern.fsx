// Tests: let rec with a tuple pattern on the left.
let r =
    let rec isEven, isOdd =
        ((fun n -> n = 0 || isOdd (n - 1)), (fun n -> n <> 0 && isEven (n - 1)))
    isEven 10
