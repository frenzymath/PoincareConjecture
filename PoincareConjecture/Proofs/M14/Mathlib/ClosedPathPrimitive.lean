import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false

open Set
open scoped Topology intervalIntegral

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ}

noncomputable def closedPathPrimitive (t₀ : Icc a b) :
    C(Icc a b, E) →L[ℝ] C(Icc a b, E) := by
  let π : C(ℝ, Icc a b) := ⟨projIcc a b (t₀.property.1.trans t₀.property.2), continuous_projIcc⟩
  let L : C(Icc a b, E) →ₗ[ℝ] C(Icc a b, E) := {
    toFun := fun v => ⟨fun r => ∫ s in (t₀ : ℝ)..(r : ℝ), v (π s),
      (intervalIntegral.continuous_primitive
        (fun c d => (v.continuous.comp π.continuous).intervalIntegrable c d) t₀.val).comp
          continuous_subtype_val⟩
    map_add' := by
      intro v w
      ext r
      exact intervalIntegral.integral_add
        ((v.continuous.comp π.continuous).intervalIntegrable _ _)
        ((w.continuous.comp π.continuous).intervalIntegrable _ _)
    map_smul' := by
      intro c v
      ext r
      exact intervalIntegral.integral_smul c _ }
  refine L.mkContinuous (b - a) ?_
  intro v
  apply (ContinuousMap.norm_le _ (mul_nonneg (sub_nonneg.mpr
    (t₀.property.1.trans t₀.property.2)) (norm_nonneg v))).2
  intro r
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (t₀ : ℝ)) (b := (r : ℝ)) (fun s _ => v.norm_coe_le_norm (π s))
  have hdist : |(r : ℝ) - t₀.val| ≤ b - a := abs_le.mpr
    ⟨by linarith [r.property.1, t₀.property.2], by linarith [r.property.2, t₀.property.1]⟩
  exact hbound.trans ((mul_le_mul_of_nonneg_left hdist (norm_nonneg v)).trans_eq (mul_comm _ _))

theorem closedPathPrimitive_apply (t₀ : Icc a b) (v : C(Icc a b, E)) (r : Icc a b) :
    closedPathPrimitive t₀ v r =
      ∫ s in (t₀ : ℝ)..(r : ℝ), v (projIcc a b (t₀.property.1.trans t₀.property.2) s) := rfl

theorem closedPathPrimitive_norm_le (t₀ : Icc a b) :
    ‖closedPathPrimitive (E := E) t₀‖ ≤ b - a := by
  unfold closedPathPrimitive
  exact LinearMap.mkContinuous_norm_le _ (sub_nonneg.mpr (t₀.property.1.trans t₀.property.2)) _

theorem closedPathPrimitive_initial (t₀ : Icc a b) (v : C(Icc a b, E)) :
    closedPathPrimitive t₀ v t₀ = 0 := by
  rw [closedPathPrimitive_apply, intervalIntegral.integral_same]

variable [CompleteSpace E]

theorem closedPathPrimitive_hasDerivWithinAt (t₀ r : Icc a b) (v : C(Icc a b, E)) :
    HasDerivWithinAt
      (fun s => closedPathPrimitive t₀ v (projIcc a b (t₀.property.1.trans t₀.property.2) s))
      (v r) (Icc a b) r.val := by
  let π : C(ℝ, Icc a b) := ⟨projIcc a b (t₀.property.1.trans t₀.property.2), continuous_projIcc⟩
  have hd := ((v.continuous.comp π.continuous).integral_hasStrictDerivAt t₀.val r.val).hasDerivAt
  have hπ : π r.val = r := projIcc_of_mem (t₀.property.1.trans t₀.property.2) r.property
  dsimp only [Function.comp_def] at hd
  rw [hπ] at hd
  apply hd.hasDerivWithinAt.congr_of_mem _ r.property
  intro s hs
  rw [closedPathPrimitive_apply, projIcc_of_mem (t₀.property.1.trans t₀.property.2) hs]
  rfl

end PoincareConjecture.M14
