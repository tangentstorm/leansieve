import Lake
open Lake DSL

package treesiv {
  -- add package configuration options here
}

lean_lib Treesiv {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe treesiv {
  root := `Main
}