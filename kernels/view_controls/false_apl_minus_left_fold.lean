import Vw
-- false: APL -/ 10 3 2 is the right fold 10-(3-2) = 9, not the left fold 5
example : Apl.redR (· - ·) [10, 3, 2] = some 5 := by decide
