import PoincareConjecture.Proofs.M09.PathSpaceCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false

open scoped ContDiff Topology intervalIntegral
open Set

namespace PoincareConjecture.Proofs.M09

noncomputable def unitTimeProjection : C(ℝ, Set.Icc (0 : ℝ) 1) :=
  ⟨Set.projIcc 0 1 zero_le_one, continuous_projIcc⟩

@[simp] theorem unitTimeProjection_of_mem {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    unitTimeProjection r = ⟨r, hr⟩ :=
  Set.projIcc_of_mem zero_le_one hr

noncomputable def unitPathIntegral : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ := by
  let L : C(Set.Icc (0 : ℝ) 1, ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun v ↦ ∫ r in (0 : ℝ)..1, v (unitTimeProjection r)
    map_add' := by
      intro v w
      exact intervalIntegral.integral_add
        ((v.continuous.comp unitTimeProjection.continuous).intervalIntegrable _ _)
        ((w.continuous.comp unitTimeProjection.continuous).intervalIntegrable _ _)
    map_smul' := by
      intro c v
      exact intervalIntegral.integral_smul c _
  }
  refine L.mkContinuous 1 ?_
  intro v
  change ‖∫ r in (0 : ℝ)..1, v (unitTimeProjection r)‖ ≤ 1 * ‖v‖
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (fun r _ ↦ v.norm_coe_le_norm (unitTimeProjection r))

@[simp] theorem unitPathIntegral_apply (v : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    unitPathIntegral v = ∫ r in (0 : ℝ)..1, v (unitTimeProjection r) := rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def scaledSegmentPath : (E × ℝ) →L[ℝ] C(Set.Icc (0 : ℝ) 1, E × ℝ) := by
  let L : (E × ℝ) →ₗ[ℝ] C(Set.Icc (0 : ℝ) 1, E × ℝ) := {
    toFun := fun z ↦ ⟨fun r ↦ (z.1, z.2 * (r : ℝ)),
      continuous_const.prodMk (continuous_const.mul continuous_subtype_val)⟩
    map_add' := by
      intro z w
      apply ContinuousMap.ext
      intro r
      change (z.1 + w.1, (z.2 + w.2) * (r : ℝ)) =
        (z.1 + w.1, z.2 * (r : ℝ) + w.2 * (r : ℝ))
      rw [add_mul]
    map_smul' := by
      intro c z
      apply ContinuousMap.ext
      intro r
      change (c • z.1, (c * z.2) * (r : ℝ)) =
        (c • z.1, c * (z.2 * (r : ℝ)))
      rw [mul_assoc]
  }
  refine L.mkContinuous 1 ?_
  intro z
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg z)).2
  intro r
  change ‖(z.1, z.2 * (r : ℝ))‖ ≤ ‖z‖
  rw [Prod.norm_def, Prod.norm_def]
  apply max_le (le_max_left _ _)
  calc
    ‖z.2 * (r : ℝ)‖ = ‖z.2‖ * |(r : ℝ)| := by simp only [norm_mul, Real.norm_eq_abs]
    _ ≤ ‖z.2‖ * 1 := mul_le_mul_of_nonneg_left
      (by rw [abs_of_nonneg r.property.1]; exact r.property.2) (norm_nonneg _)
    _ ≤ max ‖z.1‖ ‖z.2‖ := by rw [mul_one]; exact le_max_right _ _

@[simp] theorem scaledSegmentPath_apply (z : E × ℝ) (r : Set.Icc (0 : ℝ) 1) :
    scaledSegmentPath z r = (z.1, z.2 * (r : ℝ)) := rfl

theorem integral_zero_to_eq_scaled (f : ℝ → ℝ) (a : ℝ) :
    (∫ s in 0..a, f s) = a * ∫ r in (0 : ℝ)..1, f (a * r) := by
  simpa only [smul_eq_mul, mul_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) f a).symm

theorem contDiff_parameter_primitive [FiniteDimensional ℝ E]
    (g : E × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun z : E × ℝ ↦ ∫ s in 0..z.2, g (z.1, s)) := by
  let gC : C(E × ℝ, ℝ) := ⟨g, hg.continuous⟩
  have hsub := (contDiff_postcomp_smooth (K := Set.Icc (0 : ℝ) 1) gC hg).comp
    (scaledSegmentPath (E := E)).contDiff
  have havg : ContDiff ℝ ∞
      (fun z : E × ℝ ↦ unitPathIntegral (gC.comp (scaledSegmentPath z))) :=
    unitPathIntegral.contDiff.comp hsub
  have heq (z : E × ℝ) :
      unitPathIntegral (gC.comp (scaledSegmentPath z)) =
        ∫ r in (0 : ℝ)..1, g (z.1, z.2 * r) := by
    rw [unitPathIntegral_apply]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using hr
    simp only [ContinuousMap.comp_apply, unitTimeProjection_of_mem hr',
      scaledSegmentPath_apply, gC, ContinuousMap.coe_mk]
  have hresult : ContDiff ℝ ∞ (fun z : E × ℝ ↦
      z.2 * unitPathIntegral (gC.comp (scaledSegmentPath z))) := contDiff_snd.mul havg
  have hfun : (fun z : E × ℝ ↦ ∫ s in 0..z.2, g (z.1, s)) =
      (fun z : E × ℝ ↦ z.2 * unitPathIntegral (gC.comp (scaledSegmentPath z))) := by
    funext z
    rw [heq, integral_zero_to_eq_scaled]
  rw [hfun]
  exact hresult

end PoincareConjecture.Proofs.M09
