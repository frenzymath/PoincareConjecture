import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open Set

variable {X : Type*} [TopologicalSpace X] {S : Set X} {B : X → ℝ} {η : ℝ}




theorem IsPreconnected.exists_sign_mul_close (hS : IsPreconnected S)
    (hB : ContinuousOn B S) (hη : η ≤ 1)
    (hpoint : ∀ x ∈ S, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ |1 - σ * B x| < η) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ S, |1 - σ * B x| < η := by
  have hzero (x : X) (hx : x ∈ S) : B x ≠ 0 := by
    obtain ⟨σ, _, hσ⟩ := hpoint x hx
    intro hz
    rw [hz, mul_zero, sub_zero, abs_one] at hσ
    linarith
  rcases hS.mapsTo_Ioi_or_Iio hB hzero with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro x hx
    obtain ⟨σ, hσ, hclose⟩ := hpoint x hx
    rcases hσ with rfl | rfl
    · exact hclose
    · have h := hpos hx
      have habs := le_abs_self (1 - (-1) * B x)
      change 0 < B x at h
      linarith
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro x hx
    obtain ⟨σ, hσ, hclose⟩ := hpoint x hx
    rcases hσ with rfl | rfl
    · have h := hneg hx
      have habs := le_abs_self (1 - (1 : ℝ) * B x)
      change B x < 0 at h
      linarith
    · exact hclose
