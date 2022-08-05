import Lake
open Lake DSL

package pe {
}

lean_lib PE {
}

@[defaultTarget]
lean_exe pe {
  root := `Main
}
