import RakeSieve


def main : IO Unit := do
  let mut s : PrimeSieve _ := { state := RakeSieve.init }
  for _ in [0:5] do
    IO.println <| s.state.p
    s := s.next

#eval main
