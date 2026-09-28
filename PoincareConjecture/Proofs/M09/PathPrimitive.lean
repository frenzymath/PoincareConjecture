import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false

open scoped Topology intervalIntegral
open Set

namespace PoincareConjecture.Proofs.M09

noncomputable def symmetricTimeProjection : C(ℝ, Set.Icc (-1 : ℝ) 1) :=
  ⟨Set.projIcc (-1) 1 (by norm_num), continuous_projIcc⟩

@[simp] theorem symmetricTimeProjection_of_mem {r : ℝ} (hr : r ∈ Set.Icc (-1 : ℝ) 1) :
    symmetricTimeProjection r = ⟨r, hr⟩ :=
  Set.projIcc_of_mem (by norm_num) hr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def pathPrimitive :
    C(Set.Icc (-1 : ℝ) 1, E) →L[ℝ] C(Set.Icc (-1 : ℝ) 1, E) := by
  let L : C(Set.Icc (-1 : ℝ) 1, E) →ₗ[ℝ] C(Set.Icc (-1 : ℝ) 1, E) := {
    toFun := fun v ↦ ⟨fun r ↦ ∫ s in 0..(r : ℝ), v (symmetricTimeProjection s),
      (intervalIntegral.continuous_primitive
        (fun a b ↦ (v.continuous.comp symmetricTimeProjection.continuous).intervalIntegrable a b)
        0).comp continuous_subtype_val⟩
    map_add' := by
      intro v w
      ext r
      exact intervalIntegral.integral_add
        ((v.continuous.comp symmetricTimeProjection.continuous).intervalIntegrable _ _)
        ((w.continuous.comp symmetricTimeProjection.continuous).intervalIntegrable _ _)
    map_smul' := by
      intro c v
      ext r
      exact intervalIntegral.integral_smul c _
  }
  have hL : ∀ v, ‖L v‖ ≤ 1 * ‖v‖ := by
    intro v
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg v)).2
    intro r
    change ‖∫ s in 0..(r : ℝ), v (symmetricTimeProjection s)‖ ≤ ‖v‖
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := (r : ℝ)) (fun s _ ↦ v.norm_coe_le_norm (symmetricTimeProjection s))
    calc
      ‖∫ s in 0..(r : ℝ), v (symmetricTimeProjection s)‖ ≤ ‖v‖ * |(r : ℝ) - 0| := hbound
      _ ≤ ‖v‖ * 1 := mul_le_mul_of_nonneg_left
        (by simpa only [sub_zero] using (abs_le.mpr r.property)) (norm_nonneg v)
      _ = ‖v‖ := mul_one _
  exact L.mkContinuous 1 hL

@[simp] theorem pathPrimitive_apply (v : C(Set.Icc (-1 : ℝ) 1, E))
    (r : Set.Icc (-1 : ℝ) 1) :
    pathPrimitive v r = ∫ s in 0..(r : ℝ), v (symmetricTimeProjection s) := rfl

theorem pathPrimitive_norm_le :
    ‖pathPrimitive (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg v)).2
  intro r
  rw [pathPrimitive_apply]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (r : ℝ)) (fun s _ ↦ v.norm_coe_le_norm (symmetricTimeProjection s))
  exact hbound.trans ((mul_le_mul_of_nonneg_left
    (by simpa only [sub_zero] using (abs_le.mpr r.property)) (norm_nonneg v)).trans_eq
    (mul_one ‖v‖))

@[simp] theorem pathPrimitive_at_zero (v : C(Set.Icc (-1 : ℝ) 1, E)) :
    pathPrimitive v ⟨0, by norm_num⟩ = 0 := by
  simp only [pathPrimitive_apply, intervalIntegral.integral_same]

theorem pathPrimitive_hasDerivAt (v : C(Set.Icc (-1 : ℝ) 1, E))
    (r : ℝ) (_hr : r ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ ↦ ∫ s in 0..t, v (symmetricTimeProjection s))
      (v (symmetricTimeProjection r)) r :=
  ((v.continuous.comp symmetricTimeProjection.continuous).integral_hasStrictDerivAt 0 r).hasDerivAt

end PoincareConjecture.Proofs.M09
