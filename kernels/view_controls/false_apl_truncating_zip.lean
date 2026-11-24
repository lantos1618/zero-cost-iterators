import Vw
-- false: a truncating zip is not an APL shape check; misaligned extents give LENGTH ERROR
example : (Apl.ipVec [1, 2, 3] [4, 5]).toOption = some 14 := by decide
