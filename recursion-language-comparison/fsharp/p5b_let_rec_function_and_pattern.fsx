// Tests: a function binding and a tuple pattern binding in one let rec ... and group.
let r =
    let rec isEven n = n = 0 || isOdd (n - 1)
    and isOdd, unused = ((fun n -> n <> 0 && isEven (n - 1)), ())
    isEven 10
