import PoincareConjecture.Definitions.Ch12.StandardCap
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData



theorem scalar_directional_bound_of_unit_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) {B : ℝ}
    (hunit : ∀ v : TangentSpace (𝓡 n) x, g.inner x v v = 1 →
      |mvfderiv (𝓡 n) D.scalarCurvature x v| ≤ B)
    (v : TangentSpace (𝓡 n) x) :
    |mvfderiv (𝓡 n) D.scalarCurvature x v| ≤ B * g.tangentNorm x v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_cases hv : v = 0
  · subst v
    simp [RiemannianMetric.tangentNorm]
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : g.inner x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = 1 := by
    change inner ℝ (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = 1
    rw [real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h := hunit (‖v‖⁻¹ • v) hw
  rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hnorm)] at h
  have hmul := mul_le_mul_of_nonneg_left h hnorm.le
  rw [← mul_assoc, mul_inv_cancel₀ hnorm.ne', one_mul] at hmul
  have hnorm_eq : ‖v‖ = g.tangentNorm x v := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  simpa only [hnorm_eq, mul_comm] using hmul



theorem scalar_radius_directional_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) {A : ℝ}
    (hR : 0 < D.scalarCurvature x)
    (hreg : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) D.scalarCurvature x)
    (hunit : ∀ v : TangentSpace (𝓡 n) x, g.inner x v v = 1 →
      |mvfderiv (𝓡 n) D.scalarCurvature x v| ≤
        A * D.scalarCurvature x ^ (3 / 2 : ℝ))
    (v : TangentSpace (𝓡 n) x) :
    |mvfderiv (𝓡 n) (fun y => D.scalarCurvature y ^ (-1 / 2 : ℝ)) x v| ≤
      (A / 2) * g.tangentNorm x v := by
  have hrpow := Real.hasDerivAt_rpow_const (p := (-1 / 2 : ℝ)) (Or.inl hR.ne')
  have hchain : mvfderiv (𝓡 n) (fun y => D.scalarCurvature y ^ (-1 / 2 : ℝ)) x v =
      (-1 / 2 : ℝ) * D.scalarCurvature x ^ (-3 / 2 : ℝ) *
    mvfderiv (𝓡 n) D.scalarCurvature x v := by
    change mvfderiv (𝓡 n) ((fun r : ℝ => r ^ (-1 / 2 : ℝ)) ∘ D.scalarCurvature) x v = _
    rw [mvfderiv_comp_apply x hrpow.differentiableAt.mdifferentiableAt hreg v]
    simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
    change fderiv ℝ (fun r : ℝ => r ^ (-1 / 2 : ℝ)) (D.scalarCurvature x)
      (mvfderiv (𝓡 n) D.scalarCurvature x v) = _
    rw [fderiv_eq_deriv_mul, hrpow.deriv]
    norm_num [mvfderiv, ContinuousLinearMap.comp_apply]
  rw [hchain, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hR _)]
  norm_num
  have h := D.scalar_directional_bound_of_unit_bound x hunit v
  have hmul := mul_le_mul_of_nonneg_left h
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (Real.rpow_nonneg hR.le (-3 / 2 : ℝ)))
  have hcancel : D.scalarCurvature x ^ (-3 / 2 : ℝ) *
      D.scalarCurvature x ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hR]
    norm_num
  have heq : (1 / 2 * D.scalarCurvature x ^ (-3 / 2 : ℝ)) *
      (A * D.scalarCurvature x ^ (3 / 2 : ℝ) * g.tangentNorm x v) =
        A / 2 * g.tangentNorm x v := by
    calc
      _ = (A / 2 * g.tangentNorm x v) *
          (D.scalarCurvature x ^ (-3 / 2 : ℝ) * D.scalarCurvature x ^ (3 / 2 : ℝ)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  simpa only [neg_div] using hmul.trans_eq heq

end PoincareConjecture.LeviCivitaData
