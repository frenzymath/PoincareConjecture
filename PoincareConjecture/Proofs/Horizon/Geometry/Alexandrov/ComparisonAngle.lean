import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section
set_option autoImplicit false

open Filter Topology

namespace Poincare.Alexandrov

def comparisonAngle (r s t : ℝ) : ℝ :=
  Real.arccos ((Real.cosh r * Real.cosh s - Real.cosh t) /
    (Real.sinh r * Real.sinh s))

theorem comparisonAngle_nonneg (r s t : ℝ) : 0 ≤ comparisonAngle r s t :=
  Real.arccos_nonneg _

theorem comparisonAngle_le_pi (r s t : ℝ) : comparisonAngle r s t ≤ Real.pi :=
  Real.arccos_le_pi _

theorem comparisonAngle_comm (r s t : ℝ) :
    comparisonAngle r s t = comparisonAngle s r t := by
  simp only [comparisonAngle, mul_comm]

theorem comparisonCos_mem_Icc {r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 ≤ t)
    (hrs : |r - s| ≤ t) (htop : t ≤ r + s) :
    (Real.cosh r * Real.cosh s - Real.cosh t) / (Real.sinh r * Real.sinh s) ∈
      Set.Icc (-1 : ℝ) 1 := by
  have hden : 0 < Real.sinh r * Real.sinh s :=
    mul_pos (Real.sinh_pos_iff.mpr hr) (Real.sinh_pos_iff.mpr hs)
  have hupper : Real.cosh t ≤ Real.cosh (r + s) :=
    Real.cosh_le_cosh.mpr (by
      simpa only [abs_of_nonneg ht, abs_of_pos (add_pos hr hs)] using htop)
  have hlower : Real.cosh (r - s) ≤ Real.cosh t :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg ht] using hrs)
  rw [Real.cosh_add] at hupper
  rw [Real.cosh_sub] at hlower
  constructor
  · apply (le_div_iff₀ hden).mpr
    linarith
  · apply (div_le_iff₀ hden).mpr
    linarith

theorem cos_comparisonAngle {r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 ≤ t)
    (hrs : |r - s| ≤ t) (htop : t ≤ r + s) :
    Real.cos (comparisonAngle r s t) =
      (Real.cosh r * Real.cosh s - Real.cosh t) / (Real.sinh r * Real.sinh s) := by
  exact Real.cos_arccos (comparisonCos_mem_Icc hr hs ht hrs htop).1
    (comparisonCos_mem_Icc hr hs ht hrs htop).2

theorem tendsto_comparisonAngle {ι : Type*} {l : Filter ι}
    {r s t : ι → ℝ} {r₀ s₀ t₀ : ℝ}
    (hr : Tendsto r l (𝓝 r₀)) (hs : Tendsto s l (𝓝 s₀))
    (ht : Tendsto t l (𝓝 t₀)) (hr₀ : 0 < r₀) (hs₀ : 0 < s₀) :
    Tendsto (fun i => comparisonAngle (r i) (s i) (t i)) l
      (𝓝 (comparisonAngle r₀ s₀ t₀)) := by
  exact Real.continuous_arccos.continuousAt.tendsto.comp
    (((Real.continuous_cosh.tendsto _ |>.comp hr).mul
      (Real.continuous_cosh.tendsto _ |>.comp hs) |>.sub
      (Real.continuous_cosh.tendsto _ |>.comp ht)).div
      ((Real.continuous_sinh.tendsto _ |>.comp hr).mul
        (Real.continuous_sinh.tendsto _ |>.comp hs))
      (mul_ne_zero (ne_of_gt (Real.sinh_pos_iff.mpr hr₀))
        (ne_of_gt (Real.sinh_pos_iff.mpr hs₀))))

end Poincare.Alexandrov
