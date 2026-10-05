import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.FreePhaseHalfTurnLabels
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.FreePhaseSeamObservation
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.HalfTurnBoundary

/-!
# Exact normalization algebra for a rotated free phase

Whole-period corrections retain the original boundary curves and phase
lifts. Source: Lemaire 1982, Lemma 5.1, p. 99; M64 derivation
`2026-09-26-free-phase-cut-rotation.md`.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set

namespace PoincareMT

open Proofs.M58

/-- The affine period identity extends to subtraction of every integer period. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
theorem m64AffinePeriod_sub_int_mul {H : ℝ → ℝ} {D : ℝ}
    (hH : ∀ x, H (x + curvePeriod) = H x + D) (x : ℝ) (j : ℤ) :
    H (x - (j : ℝ) * curvePeriod) = H x - (j : ℝ) * D := by
  have hP : curvePeriod ≠ 0 := by unfold curvePeriod; positivity
  have hper : Function.Periodic (fun x => H x - (D / curvePeriod) * x) curvePeriod := by
    intro x
    change H (x + curvePeriod) - D / curvePeriod * (x + curvePeriod) =
      H x - D / curvePeriod * x
    rw [hH]
    field_simp [hP]
    ring
  have h := hper.sub_int_mul_eq (x := x) j
  have hcoef : D / curvePeriod * ((j : ℝ) * curvePeriod) = (j : ℝ) * D := by
    field_simp [hP]
  rw [mul_sub, hcoef] at h
  linarith

/-- The normalized half-turn label gives the same target boundary as the measurable
half-turn. Flat fibers are allowed. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449; M64 derivation 2026-09-26-free-phase-cut-rotation.md. -/
theorem m64FreePhaseHalfTurnLabel_boundary
    {X : Type*} {c : ℝ → X} (hc : Function.Periodic c curvePeriod)
    {f : ℝ → ℝ} (hf : ∀ x, f (x + curvePeriod) = f x + curvePeriod) (x : ℝ) :
    c (m64FreePhaseHalfTurnLabel f x) = c (f (m64BoundaryHalfTurn x)) := by
  rw [m64FreePhaseHalfTurnLabel_trace hc]
  dsimp only [m64BoundaryHalfTurn]
  split_ifs with hx
  · rfl
  · rw [show x + curvePeriod / 2 = (x - curvePeriod / 2) + curvePeriod by ring,
      hf, hc]

/-- The original phase lift evaluated on the normalized label has the corresponding integer
winding removed. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64
derivation 2026-09-26-free-phase-cut-rotation.md. -/
theorem m64FreePhaseHalfTurnLabel_phase
    {H f : ℝ → ℝ} {D : ℝ} (hH : ∀ x, H (x + curvePeriod) = H x + D) (x : ℝ) :
    H (m64FreePhaseHalfTurnLabel f x) =
      H (f (x + curvePeriod / 2)) - (m64FreePhaseHalfTurnFloor f : ℝ) * D :=
  m64AffinePeriod_sub_int_mul hH _ _

/-- An actual winding period makes the observed phase periodic at every real phase value,
not only at zero. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64
derivation 2026-09-26-free-phase-cut-rotation.md. -/
theorem m64AngularPoint_phase_periodic {k D : ℝ}
    (hperiod : angularPoint (k * D) = angularPoint 0) :
    Function.Periodic (fun x => angularPoint (k * x)) D := by
  intro x
  have h := m64AngularPoint_sub_phase_period hperiod (x + D)
  simpa only [add_sub_cancel_right] using h.symm

end PoincareMT
