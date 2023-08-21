import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "f287c039ed66259399f8d00ee3489ff14d4b53e6"

package «Aara» {
  -- add package configuration options here
}

lean_lib Resources where
  roots := #[`Resources]

lean_lib LetTick where
  roots := #[`LetTick]

lean_lib «Aara» {
  -- add library configuration options here
}

@[default_target]
lean_exe «Main» {
  root := `Main
}
