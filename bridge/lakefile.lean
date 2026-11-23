import Lake
open Lake DSL
package bridge
@[default_target] lean_lib Bridge
@[default_target] lean_lib Pipe
@[default_target] lean_lib Vw
@[default_target] lean_exe i8check where root := `Main
@[default_target] lean_exe pipegen where root := `PipeGen
@[default_target] lean_exe vwtest where root := `VwTest
@[default_target] lean_exe gendemo where root := `GenDemo
@[default_target] lean_lib TaskCore
@[default_target] lean_exe tasks where root := `Tasks
@[default_target] lean_exe taskcheck where root := `TaskCheck
