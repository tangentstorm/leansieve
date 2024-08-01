-- https://leanprover-community.github.io/lean4-metaprogramming-book/-- import Mathlib.Tactic
open Nat

inductive JN : Type where
  | i : Int → JN
  | a : Array Nat → JN
  | e : String → JN -- error
deriving Repr

abbrev S := String
inductive JV : Type where
  | mo : S → (JN → JN) → JV
  | dy : S → (JN → JN → JN) → JV
  | am : S → (Option JN → JN → JN) → JV

instance : Repr JV where
  reprPrec j _ := match j with
    | JV.mo s _ => s
    | JV.dy s _ => s
    | _ => "??"

inductive J : Type where
  | n : JN → J
  | v : JV → J
  | e : String → J
deriving Repr

declare_syntax_cat jx -- j expression
syntax num : jx
syntax " ι " jx: jx
syntax " ⟪ " jx " ⟫ " : term

def apply_mo (v:JV) (y:JN) : JN :=
  match v with
   | JV.mo _ f => f y
   | JV.dy s _ => JN.e s!"{s}: valance"
   | JV.am _ f => f none y

def juxt (a:J) (b:J) : J := match a, b with
  | (J.v v), (J.n y) => apply_mo v y |> J.n
  | _, _ => J.e "nyi"

def iota (y:JN) : JN :=
  match y with
  | JN.i n =>
    if n≥0 then JN.a <| Array.range n.toNat else JN.e "ι: expect y pos"
  | _ => JN.e "ι : bad argument"

macro_rules
 | `(⟪ $num:num ⟫) => `(J.n (JN.i $num))
 | `(⟪ ι $y:jx ⟫) => `(juxt (J.v <| JV.mo "ι" iota) ⟪ $y ⟫ )

#check ⟪ ι 10 ⟫

def x : Nat := 10
def xs : Std.Range := [0:10]
