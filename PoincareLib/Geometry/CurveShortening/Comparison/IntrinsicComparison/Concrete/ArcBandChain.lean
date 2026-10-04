import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Cap.PatchArcBands

/-! Concrete data for an occupied chain of actual linear-coordinate bands.
Source: MT Claim 19.40, pp. 470-471; three-arc cap/patch seed derivation,
Section 5. This record retains the original arc and literal physical cuts. -/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology
open PoincareMT.Topology.Surface

namespace PoincareMT

/-- A positive finite chain of actual occupied bands on a prescribed original arc interval,
with exact physical cuts and mutual contacts. Source: MT Claim 19.40; three-arc cap/patch
seed, Section 5. Source:
`proof-work/tasks/M64/derivations/2026-09-27-three-arc-cap-patch-seed.md`, Section 5. -/
structure M64IntrinsicArcBandChain (gamma : ℝ → AnnulusCoordinates)
    (a b : ℝ) (U : Set AnnulusCoordinates) where
  count : ℕ
  count_pos : 0 < count
  cut : Fin (count + 1) → ℝ
  cut_strictMono : StrictMono cut
  first_cut : cut 0 = a
  last_cut : cut (Fin.last count) = b
  direction : ℝ → AnnulusCoordinates
  frame : Fin count → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)
  parameter : Fin count → OpenPartialHomeomorph ℝ ℝ
  graph : Fin count → ℝ → ℝ
  length : ℝ
  length_pos : 0 < length
  band : ∀ i : Fin count,
    ObliqueBandFaces
      (collarParameterEquiv.trans (frame i).symm).toHomeomorph.toOpenPartialHomeomorph
      (graph i) (parameter i (cut i.castSucc)) (parameter i (cut i.succ))
      (frame i (direction (cut i.castSucc))).1 (frame i (direction (cut i.castSucc))).2
      (frame i (direction (cut i.succ))).1 (frame i (direction (cut i.succ))).2 length length
  lower_arc : ∀ i, (band i).lowerArc = gamma '' Icc (cut i.castSucc) (cut i.succ)
  left_cut : ∀ i, (band i).leftCut = segment ℝ (gamma (cut i.castSucc))
    (gamma (cut i.castSucc) + length • direction (cut i.castSucc))
  right_cut : ∀ i, (band i).rightCut = segment ℝ (gamma (cut i.succ))
    (gamma (cut i.succ) + length • direction (cut i.succ))
  occupied : ∀ i, (band i).carrier ⊆ closure U
  off_lower : ∀ i, (band i).carrier \ (band i).lowerArc ⊆ U
  separated : ∀ i j : Fin count, i.succ < j.castSucc →
    Disjoint (band i).carrier (band j).carrier
  adjacent : ∀ i j : Fin count, i.succ = j.castSucc →
    (band i).carrier ∩ (band j).carrier = segment ℝ (gamma (cut i.succ))
      (gamma (cut i.succ) + length • direction (cut i.succ))

namespace M64IntrinsicArcBandChain

/-- Every actual lower arc stays in the chain's prescribed original interval. Source: MT
Claim 19.40; three-arc cap/patch seed, Section 5. Source:
`proof-work/tasks/M64/derivations/2026-09-27-three-arc-cap-patch-seed.md`, Section 5. -/
theorem lower_subset {gamma : ℝ → AnnulusCoordinates} {a b : ℝ}
    {U : Set AnnulusCoordinates} (C : M64IntrinsicArcBandChain gamma a b U)
    (i : Fin C.count) : (C.band i).lowerArc ⊆ gamma '' Icc a b := by
  rw [C.lower_arc]
  apply image_mono
  apply Icc_subset_Icc
  · simpa only [C.first_cut] using C.cut_strictMono.monotone (Fin.zero_le i.castSucc)
  · simpa only [C.last_cut] using C.cut_strictMono.monotone (Fin.le_last i.succ)

end M64IntrinsicArcBandChain

end PoincareMT
