import Lake
open Lake DSL

package treesiv {}

lean_lib Treesiv {}
lean_lib PrimeGen { }
lean_lib PrimeSieve { }
lean_lib ASeq { }
lean_lib Rake { }
lean_lib RakeMap { }
lean_lib RakeSieve { }

@[default_target]
lean_exe treesiv {
  root := `Main}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
