import Batteries.Data.Rat.Basic

structure CKey (α:Type) where
  key: κ
  val: α
  trans: Transition

structure Point (α:Type) where
  x : α
  y : α


structure RGB where
  r : Fin 256
  g : Fin 256
  b : Fin 256



structure Tile where
  label : String
  xy : Point Rat
  wh : Point Rat
  color : RGB
