import Lake
open Lake DSL

package pe {
}

lean_lib PE {
}

lean_lib PE2 {
}

@[defaultTarget]
lean_exe pe {
  root := `Main
}

lean_exe sieve {
  root := `Sieve
}
