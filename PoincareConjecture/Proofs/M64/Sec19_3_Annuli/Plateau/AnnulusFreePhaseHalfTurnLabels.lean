import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.LiftNormalization

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology

namespace PoincareConjecture

local notation "P" => curvePeriod
local notation "a" => curvePeriod / 2

def m64FreePhaseHalfTurnFloor (f : ℝ → ℝ) : ℤ :=
  ⌊f a / P⌋

def m64FreePhaseHalfTurnLabel (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (x + a) - (m64FreePhaseHalfTurnFloor f : ℝ) * P

def m64FreePhaseHalfTurnOrderIso (H : ℝ ≃o ℝ) (f : ℝ → ℝ) : ℝ ≃o ℝ :=
  (OrderIso.addRight ((m64FreePhaseHalfTurnFloor f : ℝ) * P)).trans H

theorem m64FreePhaseHalfTurnLabel_monotone
    {f : ℝ → ℝ} (hf : Monotone f) :
    Monotone (m64FreePhaseHalfTurnLabel f) := by
  intro x y hxy
  simpa only [m64FreePhaseHalfTurnLabel, add_comm x a, add_comm y a] using
    sub_le_sub_right (hf (add_le_add_right hxy a)) _

theorem m64FreePhaseHalfTurnLabel_period
    {f : ℝ → ℝ} (hf : ∀ x, f (x + P) = f x + P) (x : ℝ) :
    m64FreePhaseHalfTurnLabel f (x + P) =
      m64FreePhaseHalfTurnLabel f x + P := by
  dsimp [m64FreePhaseHalfTurnLabel]
  rw [show x + P + a = (x + a) + P by ring, hf]
  ring

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

theorem m64FreePhaseHalfTurnLabel_trace
    {X : Type*} {c : ℝ → X} (hc : Function.Periodic c P)
    {f : ℝ → ℝ} (x : ℝ) :
    c (m64FreePhaseHalfTurnLabel f x) = c (f (x + a)) := by
  dsimp [m64FreePhaseHalfTurnLabel]
  exact hc.sub_int_mul_eq (m64FreePhaseHalfTurnFloor f)

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

end PoincareConjecture
