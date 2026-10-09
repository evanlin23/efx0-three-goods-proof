import EFX
import Lean

/-!
# Axiom check (run by CI)

Fails unless every declaration in the `EFX` library depends only on Lean's three standard axioms:
`propext`, `Classical.choice` and `Quot.sound`. An unfinished proof, `native_decide`
(`Lean.ofReduceBool`) and any new `axiom` each add another axiom, so each fails the check.

Run from `lean/`: `lake env lean CheckAxioms.lean`
-/

open Lean Elab Command in
/-- Check every constant defined in a module of the `EFX` library. -/
elab "#check_EFX_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let inLibrary (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => (`EFX).isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false
  let mut checked : Nat := 0
  let mut bad : Array MessageData := #[]
  for (name, _) in env.constants.toList do
    if inLibrary name then
      checked := checked + 1
      for ax in ← collectAxioms name do
        unless allowed.contains ax do bad := bad.push m!"{name} uses {ax}"
  if checked == 0 then throwError "no declarations found in the EFX library"
  unless bad.isEmpty do
    throwError m!"non-standard axioms:{indentD (MessageData.joinSep bad.toList Format.line)}"
  logInfo m!"{checked} declarations in the EFX library use only propext, Classical.choice, Quot.sound"

#check_EFX_axioms

