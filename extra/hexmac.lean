import Lean

open Lean Elab Term Meta Parser

declare_syntax_cat binary
syntax bit := "▓"<|>"░"
syntax (name:=bits) many1(bit) : term
syntax foo := "{{.*" -- jstuff "}}"
syntax (name:=coolbits) " %[" (bits <|> foo <|> num)* "] " : term
#check ░░░▓░░▓░

@[term_elab]

syntax:10 (name := hexy) " $" hexitsterm:11 : term

def parseHex (s : String) : Nat :=
  s.foldl (fun acc c => 16 * acc + c.toNat.digitToNat) 0

@[macro "ob" num:str] def hexNum : Macro :=
  fun stx => do
    let some numStr := num.isStrLit?
      | throw <| Macro.Exception.error stx "expected string literal"
    let hexValue := parseHex numStr
    return mkNatLit hexValue

#eval $xff -- Should evaluate to 255
#eval %:obobob -- Should evaluate to 16
