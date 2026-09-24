/-
  ramsey/keynes_ramsey_flag.lean — scope flag for the Keynes–Ramsey track.

  This file is deliberately trivial. It is NOT part of the canonical audit run and
  proves nothing about Ramsey or Keynes. It exists so that the directory has a
  Lean anchor with a date, to which the real formalisation (see README.md) will
  be attached. Do not cite this file as a result.
-/

namespace KeynesRamsey

/-- Date on which the track was flagged (centenary year of *Truth and Probability*). -/
def flagDate : String := "2026-09-24"

/-- Planned item numbers, mirroring README.md. -/
inductive PlannedItem
  | objectionMap        -- 1. Ramsey 1922/1926 objections → Part II ledger numbers
  | representationSide  -- 2. Dutch-book route vs axiom (vii) + Ch. XV, same kernel
  | seamHypothesis      -- 3. disagreement located at the extensional/intensional seam
  deriving Repr

#check flagDate
#check PlannedItem.seamHypothesis

end KeynesRamsey
