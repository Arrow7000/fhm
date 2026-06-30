module SelfInMutual exposing (main)

-- Discriminator: a mutual group where member `p` ALSO calls ITSELF at a
-- different type (`p [ xs ]` at List (List a)). If self-references are
-- monomorphic even inside a mutual group, this must FAIL on `p [ xs ]`,
-- even though the cross-call `q xs` / `p xs` is fine.

import Html


main : Html.Html msg
main =
    let
        p : List a -> Int
        p xs =
            case xs of
                [] ->
                    q xs

                _ :: _ ->
                    p [ xs ]

        q : List a -> Int
        q xs =
            p xs
    in
    Html.text (String.fromInt (p [ 1, 2, 3 ]))
