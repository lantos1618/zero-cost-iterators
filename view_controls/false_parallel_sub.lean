import Vw
-- false: chunked reduction with subtraction differs from the ordered fold
example : (([10, 3, 2] : List Int).foldl (· - ·) 0) = ((Vw.blocks 2 ([10, 3, 2] : List Int)).map (·.foldl (· - ·) 0)).foldl (· - ·) 0 := by decide
