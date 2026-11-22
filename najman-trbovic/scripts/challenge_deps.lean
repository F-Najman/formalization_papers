module

/-
Helper of `scripts/make_challenge.py` (not part of the library). It reads the compared declarations from
`.lake/challenge_targets.txt` and prints, as tab-separated lines, every declaration of the library that the Challenge
has to copy: the declarations of the `NajmanTrbovic` modules used, transitively, by the statements (the types of the
compared declarations) and by the types and values of the definitions, instances and inductive types they use
(including the proofs generated inside those values). Theorems of the library that these values use are listed too;
the Challenge states them and Comparator compares them by their statements. Each line is
  role, module index (import order), module, first line, last line, kind, name
where role is `target` for a compared declaration and `dep` otherwise. Run (from the project directory, after
`lake build`): lake env lean scripts/challenge_deps.lean
It imports every module of the library with `import all`, because the declaration ranges and the proofs inside
definitions are private data of each module; `make_challenge.py` checks that the list below is complete.
-/
import all NajmanTrbovic
import all NajmanTrbovic.AffinePoints
import all NajmanTrbovic.AffinePointVariableChange
import all NajmanTrbovic.CubicFieldModel
import all NajmanTrbovic.CubicIntegralSplitting
import all NajmanTrbovic.CubicInvariantSplitting
import all NajmanTrbovic.CubicLifts
import all NajmanTrbovic.CubicLocal
import all NajmanTrbovic.CubicMarkedCertificate
import all NajmanTrbovic.CubicMarkedData
import all NajmanTrbovic.CubicMarkedEquation
import all NajmanTrbovic.CubicMarkedModel
import all NajmanTrbovic.CubicMarkedParameters
import all NajmanTrbovic.CubicModel
import all NajmanTrbovic.CubicProjection
import all NajmanTrbovic.CubicRoots
import all NajmanTrbovic.CubicTensor
import all NajmanTrbovic.Errata
import all NajmanTrbovic.FieldSpecialization
import all NajmanTrbovic.Homogeneous
import all NajmanTrbovic.InfinitudeData
import all NajmanTrbovic.Infinitude
import all NajmanTrbovic.LocalSquareclasses
import all NajmanTrbovic.MarkedOrderFourteen
import all NajmanTrbovic.MarkedTorsionNormalForm
import all NajmanTrbovic.Models
import all NajmanTrbovic.MultiplicativeReduction
import all NajmanTrbovic.NormData
import all NajmanTrbovic.NormObstruction
import all NajmanTrbovic.PolynomialCertificate
import all NajmanTrbovic.PrimeLifting
import all NajmanTrbovic.QuadraticFields
import all NajmanTrbovic.QuadraticSplitting
import all NajmanTrbovic.RealFields
import all NajmanTrbovic.SmallPrimeSplitting
import all NajmanTrbovic.Squareclasses
import all NajmanTrbovic.Table2Congruences
import all NajmanTrbovic.Table2
import all NajmanTrbovic.Table2ModFive
import all NajmanTrbovic.Table2Reciprocity
import all NajmanTrbovic.Table7
import all NajmanTrbovic.TorsionToMarked
import all NajmanTrbovic.TwoTorsionSplitting
import all NajmanTrbovic.Witnesses
public import Lean.Elab.Command
open Lean Elab Command

namespace ChallengeDeps

meta def inProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`NajmanTrbovic).isPrefixOf (env.header.moduleNames[idx.toNat]!)
  | none => false

/-- Generated constants that belong to the inductive type named by their prefix. -/
meta def generated : List String :=
  ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below", "brecOn", "binductionOn", "ibelow",
   "ctorIdx", "toCtorIdx", "ofNat", "induct", "sizeOf_spec", "injEq", "inj", "ctorElim", "ctorElimType"]

/-- The source declaration that produced a constant: constructors, recursors and projections belong to their
inductive type, and auxiliary constants (`foo.match_1`, `foo._proof_1`, `foo.eq_1`, ...) to `foo`. -/
meta partial def rootOf (env : Environment) (n : Name) : Name := Id.run do
  -- the module system refers to some public declarations by private aliases
  if let some u := privateToUserName? n then
    if (env.find? u).isSome then return rootOf env u
  if let some (.ctorInfo c) := env.find? n then return rootOf env c.induct
  if let some (.recInfo _) := env.find? n then return rootOf env n.getPrefix
  if let some info := env.getProjectionFnInfo? n then
    if let some (.ctorInfo c) := env.find? info.ctorName then return rootOf env c.induct
  let rec strip : Name → Name
    | .str p s =>
      if s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
          s == "eq_def" then strip p
      else if generated.contains s && (match env.find? p with | some (.inductInfo _) => true | _ => false) then p
      else .str p s
    | .num p _ => strip p
    | m => m
  let m := strip n
  if let some u := privateToUserName? m then
    if (env.find? u).isSome then return rootOf env u
  return m

meta def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"

elab "#challenge_deps" : command => do
  let env ← getEnv
  let targets := ((← IO.FS.lines ".lake/challenge_targets.txt").filter (· ≠ "")).map String.toName
  let mut work : Array Name := #[]
  for n in targets do
    let some ci := env.find? n | throwError "unknown target {n}"
    work := work ++ ci.type.getUsedConstants
  let mut seen : NameSet := {}
  let mut roots : NameSet := {}
  while h : work.size > 0 do
    let c := work.back
    work := work.pop
    if seen.contains c || !inProject env c then continue
    seen := seen.insert c
    let r := rootOf env c
    unless roots.contains r do
      roots := roots.insert r
      work := work.push r
    let some ci := env.find? c | continue
    work := work ++ ci.type.getUsedConstants
    -- The proof of a theorem of the library is not followed: such a theorem is stated in the Challenge and compared
    -- by its statement. Auxiliary theorems generated inside a definition (`foo._proof_1`) are followed.
    let userTheorem := ci matches .thmInfo _ && r == c
    if let some v := ci.value? (allowOpaque := true) then
      unless userTheorem do work := work ++ v.getUsedConstants
    if let .inductInfo v := ci then
      for ctor in v.ctors do
        if let some cc := env.find? ctor then work := work ++ cc.type.getUsedConstants
  let line (role : String) (r : Name) : CommandElabM String := do
    let some ci := env.find? r | throwError "unknown {r}"
    let some idx := env.getModuleIdxFor? r | throwError "{r} is not imported"
    let some rng ← findDeclarationRanges? r | throwError "no declaration range for {r}"
    return s!"{role}\t{idx.toNat}\t{env.header.moduleNames[idx.toNat]!}\t{rng.range.pos.line}\t{rng.range.endPos.line}\t{kindOf ci}\t{r}"
  let mut out := #[]
  for r in roots.toList do
    unless targets.contains r do out := out.push (← line "dep" r)
  for r in targets do out := out.push (← line "target" r)
  IO.println (String.intercalate "\n" out.toList)

end ChallengeDeps

#challenge_deps
