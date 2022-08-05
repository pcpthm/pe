import PE
import Lean

open Lean
open Lean.Parser.Term
open Lean.Elab.Term

class Answer (α : Type) where
  toString : α → IO String

def problemNumbers := [1:20+1].toArray

elab "getAnswerMatch%" : term => do
  let mut alts := #[]
  for n in problemNumbers do
    let pe := (`PE).append s!"P{n}"
    let n := quote n
    let parse := pe.append "parse"
    let solve := pe.append "solve"
    let value ← if (← getEnv).contains parse then
      `($(mkIdent solve) ($(mkIdent parse):ident lines) input)
    else
      `($(mkIdent solve) input)
    alts := alts.push $ ← `(matchAltExpr| | $n => $value)
  alts := alts.push $ ← `(matchAltExpr| | _ => panic! "Not implemented")
  let stx ← `(fun n lines input => match n with $alts:matchAlt*)
  return ← elabTerm stx none

def getAnswer : Nat → Array String → Nat → Nat := getAnswerMatch%

def main : IO Unit := do
  let inputs ← (·.map (·.toNat!)) <$> IO.FS.lines ("data" / "input.txt")
  for n in problemNumbers do
    let lines ← try
      IO.FS.lines ("data" / s!"p{n}.txt")
      catch _ => pure #[]
    let input := inputs[n-1]!
    let answer := getAnswer n lines input
    println! "Problem {n}: {answer}"
