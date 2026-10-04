import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.WeakPhaseClass
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.BoundaryCompactness.Lift.Normalization

/-! Labels and phase lifts for the half-period cut rotation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology

namespace PoincareMT

local notation "P" => curvePeriod
local notation "a" => curvePeriod / 2

/-- Choose the integer period that normalizes the label at the new angular origin. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
def m64FreePhaseHalfTurnFloor (f : ℝ → ℝ) : ℤ :=
  ⌊f a / P⌋

/-- Translate a label by half a period and subtract its normalizing integer period. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
def m64FreePhaseHalfTurnLabel (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (x + a) - (m64FreePhaseHalfTurnFloor f : ℝ) * P

/-- Translate the input of an order-isomorphic phase lift to compensate label normalization.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
def m64FreePhaseHalfTurnOrderIso (H : ℝ ≃o ℝ) (f : ℝ → ℝ) : ℝ ≃o ℝ :=
  (OrderIso.addRight ((m64FreePhaseHalfTurnFloor f : ℝ) * P)).trans H

/-- Half-turn label normalization preserves monotonicity, including flat fibers. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
theorem m64FreePhaseHalfTurnLabel_monotone
    {f : ℝ → ℝ} (hf : Monotone f) :
    Monotone (m64FreePhaseHalfTurnLabel f) := by
  intro x y hxy
  simpa only [m64FreePhaseHalfTurnLabel, add_comm x a, add_comm y a] using
    sub_le_sub_right (hf (add_le_add_right hxy a)) _

/-- Half-turn label normalization preserves the degree-one period identity. Proof expansion
for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
theorem m64FreePhaseHalfTurnLabel_period
    {f : ℝ → ℝ} (hf : ∀ x, f (x + P) = f x + P) (x : ℝ) :
    m64FreePhaseHalfTurnLabel f (x + P) =
      m64FreePhaseHalfTurnLabel f x + P := by
  dsimp [m64FreePhaseHalfTurnLabel]
  rw [show x + P + a = (x + a) + P by ring, hf]
  ring

/-- The normalized half-turn label at zero belongs to the half-open fundamental interval.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
theorem m64FreePhaseHalfTurnLabel_normalized
    {f : ℝ → ℝ} :
    m64FreePhaseHalfTurnLabel f 0 ∈ Ico (0 : ℝ) P := by
  have hP : 0 < P := by unfold curvePeriod; positivity
  have hlo : (m64FreePhaseHalfTurnFloor f : ℝ) ≤ f a / P :=
    Int.floor_le _
  have hhi : f a / P < (m64FreePhaseHalfTurnFloor f : ℝ) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (f a / P)
  simp only [m64FreePhaseHalfTurnLabel, zero_add]
  change f a - (m64FreePhaseHalfTurnFloor f : ℝ) * P ∈ Ico (0 : ℝ) P
  constructor
  · have h := (le_div_iff₀ hP).mp hlo
    change (m64FreePhaseHalfTurnFloor f : ℝ) * P ≤ f a at h
    exact sub_nonneg.mpr h
  · have h := (div_lt_iff₀ hP).mp hhi
    apply sub_lt_iff_lt_add.mpr
    convert h using 1
    ring

/-- A periodic target curve has the same value on the normalized and shifted labels. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
theorem m64FreePhaseHalfTurnLabel_trace
    {X : Type*} {c : ℝ → X} (hc : Function.Periodic c P)
    {f : ℝ → ℝ} (x : ℝ) :
    c (m64FreePhaseHalfTurnLabel f x) = c (f (x + a)) := by
  dsimp [m64FreePhaseHalfTurnLabel]
  exact hc.sub_int_mul_eq (m64FreePhaseHalfTurnFloor f)

/-- The adjusted phase lift cancels the label's normalizing period exactly. Proof expansion
for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
theorem m64FreePhaseHalfTurnOrderIso_apply
    (H : ℝ ≃o ℝ) (f : ℝ → ℝ) (x : ℝ) :
    m64FreePhaseHalfTurnOrderIso H f
        (m64FreePhaseHalfTurnLabel f x) = H (f (x + a)) := by
  simp only [m64FreePhaseHalfTurnOrderIso, OrderIso.trans_apply]
  change H ((OrderIso.addRight ((m64FreePhaseHalfTurnFloor f : ℝ) * P))
      (m64FreePhaseHalfTurnLabel f x)) = H (f (x + a))
  simp only [OrderIso.addRight_apply]
  congr 1
  dsimp [m64FreePhaseHalfTurnLabel]
  ring

/-- The adjusted order-isomorphic phase lift retains its affine period increment. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
theorem m64FreePhaseHalfTurnOrderIso_period
    {H : ℝ ≃o ℝ} {f : ℝ → ℝ}
    {D : ℝ} (hH : ∀ x, H (x + P) = H x + D)
    (x : ℝ) :
    m64FreePhaseHalfTurnOrderIso H f
        (x + P) = m64FreePhaseHalfTurnOrderIso H f x + D := by
  simp only [m64FreePhaseHalfTurnOrderIso, OrderIso.trans_apply,
    OrderIso.addRight_apply]
  rw [show x + P + (m64FreePhaseHalfTurnFloor f : ℝ) * P =
      (x + (m64FreePhaseHalfTurnFloor f : ℝ) * P) + P by ring, hH]

end PoincareMT
