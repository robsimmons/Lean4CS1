import Lake
open Lake DSL

package «fp-course» where
  name := "fp-course"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib «FPCourse» where
  globs := #[.andSubmodules `FPCourse]

lean_lib «Distillate» where
  globs := #[.andSubmodules `Distillate]
