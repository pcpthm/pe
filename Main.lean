import PE
import Lean

open Lean
open Lean.Parser.Term

class Answer (α : Type) where
  toString : α → IO String

instance : Answer Nat := ⟨fun n => pure $ toString n⟩

instance : Answer (IO Nat) := ⟨fun n => do Answer.toString (← n)⟩

def problemNumbers := [1:11].toArray

macro "getAnswerMatch%" : term => do
  let mut alts := #[]
  for n in problemNumbers do
    let nameSpace := (`PE).append s!"P{n}"
    let answer := mkIdent (nameSpace.append "answer")
    alts := alts.push $ ← `(matchAltExpr| | $(quote n) => Answer.toString $answer)
  alts := alts.push $ ← `(matchAltExpr| | _ => pure "Not implemented")
  `(fun $alts:matchAlt*)

def getAnswer : Nat → IO String := getAnswerMatch%

def main : IO Unit := do
  for n in problemNumbers do
    let answer ← getAnswer n
    println! "Problem {n}: {answer}"
