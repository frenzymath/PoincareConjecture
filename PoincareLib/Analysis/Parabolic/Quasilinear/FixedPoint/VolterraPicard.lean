/- Adapted from Mapher `PoincareMT/Proofs/M03/Existence/VolterraPicard.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.RicciFlow.Local.DeTurck.Gauge.DeTurckGaugeSign

/-!
# Explicit Volterra state path

This is the elementary propagator used by a native fixed-point construction.
For a continuous Banach-valued source it defines the state by an actual
interval integral and proves the initial value and the within-interval
derivative.  No parabolic or geometric solver is hidden in this definition.
-/

set_option autoImplicit false

namespace PoincareMT

open Set

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- The state obtained from an initial value and a time-dependent source. -/
noncomputable def volterraPath (x₀ : E) (f : ℝ → E) (t : ℝ) : E :=
  x₀ + ∫ s in (0 : ℝ)..t, f s

@[simp] theorem volterraPath_zero (x₀ : E) (f : ℝ → E) :
    volterraPath x₀ f 0 = x₀ := by
  simp [volterraPath]

theorem hasDerivWithinAt_volterraPath_Ico
    {x₀ : E} {f : ℝ → E} {T t : ℝ}
    (hf : ContinuousOn f (Ico (0 : ℝ) T)) (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (volterraPath x₀ f) (f t) (Ico (0 : ℝ) T) t := by
  exact (DeTurckNative.integral_hasDerivWithinAt_Ico hf ht).const_add x₀

theorem hasDerivWithinAt_volterraPath_Icc
    {x₀ : E} {f : ℝ → E} {T t : ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (volterraPath x₀ f) (f t) (Icc (0 : ℝ) T) t := by
  have hft : ContinuousOn f (Icc (0 : ℝ) t) :=
    hf.mono (Icc_subset_Icc le_rfl ht.2)
  letI : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
  have hderiv : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, f s)
      (f t) (Icc (0 : ℝ) T) t :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (hft.intervalIntegrable_of_Icc ht.1)
      (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hf t ht)
  exact hderiv.const_add x₀

/-- The Volterra state is continuous on every compact subinterval of its
source domain. -/
theorem continuousOn_volterraPath_Icc
    {x₀ : E} {f : ℝ → E} {T : ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    ContinuousOn (volterraPath x₀ f) (Icc (0 : ℝ) T) := by
  intro t ht
  exact (hasDerivWithinAt_volterraPath_Icc hf ht).continuousWithinAt

end PoincareMT
