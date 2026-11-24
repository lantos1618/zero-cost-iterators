import Lake
open Lake DSL
package iter
@[default_target] lean_lib Iter
lean_lib TaskCore
@[default_target] lean_exe tasks where root := `Tasks
@[default_target] lean_exe taskcheck where root := `TaskCheck
@[default_target] lean_exe bench where root := `Bench
@[default_target] lean_exe gencpp where root := `GenCpp
