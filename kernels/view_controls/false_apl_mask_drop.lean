import Vw
-- false: compress keeps every mask-selected element
example : (Apl.compress [true, false, true] ([5, 6, 7] : List Int)).toOption = some [5] := by decide
