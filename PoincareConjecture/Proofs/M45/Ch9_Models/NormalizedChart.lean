import PoincareConjecture.Proofs.M45.Ch9_Models.LocalScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarScaling
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M45

open PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem model_scale_three_halves {Q : ℝ} (hQ : 0 < Q) :
    Q * Real.sqrt Q = Q ^ (3 / 2 : ℝ) := by
  calc
    _ = Q ^ (1 : ℝ) * Q ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = Q ^ (1 + 1 / 2 : ℝ) := (Real.rpow_add hQ _ _).symm
    _ = _ := by norm_num

theorem model_differential_bound_of_rescaled
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g) {Q : ℝ} (hQ : 0 < Q)
    (x : E) {C : ℝ}
    (hbound : ∀ v : E, (m01RescaledMetric g Q hQ).inner x v v = 1 →
      |fderiv ℝ (m01RescaledMetric_connection g D Q hQ).scalarCurvature x v| ≤ C)
    (v : E) (hv : g.inner x v v = 1) :
    |fderiv ℝ D.scalarCurvature x v| ≤ C * Q ^ (3 / 2 : ℝ) := by
  let DQ := m01RescaledMetric_connection g D Q hQ
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hS : DQ.scalarCurvature = fun y => Q⁻¹ * D.scalarCurvature y := by
    funext y
    have h := M13.homothety_scalarCurvature_eq g (m01RescaledMetric g Q hQ)
      (Diffeomorph.refl (𝓡 3) E ∞) Q hQ (rescaledMetric_identity_homothety hQ) D DQ y
    simpa only [Diffeomorph.coe_refl, id_eq, div_eq_mul_inv, mul_comm] using h
  let w : E := (Real.sqrt Q)⁻¹ • v
  have hw : (m01RescaledMetric g Q hQ).inner x w w = 1 := by
    change Q * g.inner x ((Real.sqrt Q)⁻¹ • v) ((Real.sqrt Q)⁻¹ • v) = 1
    simp only [map_smul, smul_apply, smul_eq_mul, hv, mul_one]
    rw [M13.inv_sqrt_mul_inv_sqrt Q hQ.le, mul_inv_cancel₀ hQ.ne']
  have hder : fderiv ℝ DQ.scalarCurvature x w =
      Q⁻¹ * ((Real.sqrt Q)⁻¹ * fderiv ℝ D.scalarCurvature x v) := by
    rw [hS, fderiv_const_mul ((contDiff_scalarCurvature D).differentiable
      (by simp) x)]
    simp only [w, smul_apply, map_smul, smul_eq_mul]
    ring
  have h := hbound w hw
  change |fderiv ℝ DQ.scalarCurvature x w| ≤ C at h
  rw [hder, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hQ),
    abs_of_pos (inv_pos.mpr hsqrt)] at h
  have hscale := mul_le_mul_of_nonneg_left h (mul_pos hQ hsqrt).le
  have heq : (Q * Real.sqrt Q) *
      (Q⁻¹ * ((Real.sqrt Q)⁻¹ * |fderiv ℝ D.scalarCurvature x v|)) =
      |fderiv ℝ D.scalarCurvature x v| := by
    field_simp
  rw [heq, model_scale_three_halves hQ, mul_comm] at hscale
  exact hscale

theorem model_analytic_of_normalized_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (gE : RiemannianMetric 3 E) (DE : LeviCivitaData gE)
    {Q Cg Ce : ℝ} (hQ : 0 < Q) (hCg : 0 < Cg) (hCe : 0 < Ce)
    {f : E → M} {U : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ u v : E,
      gE.inner y u v = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y u)
        (mfderiv (𝓡 3) (𝓡 3) f y v))
    (hscalar : Q ≤ D.scalarCurvature (f 0))
    (hgradient : ∀ v : E, (m01RescaledMetric gE Q hQ).inner 0 v v = 1 →
      |fderiv ℝ (m01RescaledMetric_connection gE DE Q hQ).scalarCurvature 0 v| ≤ Cg)
    (hevolution :
      let DQ := m01RescaledMetric_connection gE DE Q hQ
      |DQ.laplacian DQ.scalarCurvature 0 + 2 * DQ.ricciNormSq 0| ≤ Ce) :
    M45PointwiseAnalyticEstimate g D (f 0) (max Cg Ce) := by
  have hR : 0 < D.scalarCurvature (f 0) := lt_of_lt_of_le hQ hscalar
  refine ⟨hR, model_scalarGradientNorm_le g D (f 0) ?_, ?_⟩
  · intro v hv
    let L := mfderiv (𝓡 3) (𝓡 3) f 0
    let w : E := L.inverse v
    have hLw : L w = v := (hinv 0 hzero).self_apply_inverse v
    have hw : gE.inner 0 w w = 1 := by
      rw [hmetric 0 hzero]
      change g.inner (f 0) (L w) (L w) = 1
      rw [hLw]
      exact hv
    have hd := model_scalar_differential_eq_of_local_isometry DE D hU hf hmetric hzero w
    have hd' : fderiv ℝ DE.scalarCurvature 0 w =
        mvfderiv (𝓡 3) D.scalarCurvature (f 0) v := by
      change mvfderiv (𝓡 3) DE.scalarCurvature 0 w =
        mvfderiv (𝓡 3) D.scalarCurvature (f 0) (L w) at hd
      rw [hLw] at hd
      simpa only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] using! hd
    rw [← hd']
    calc
      _ ≤ Cg * Q ^ (3 / 2 : ℝ) :=
        model_differential_bound_of_rescaled gE DE hQ 0 hgradient w hw
      _ ≤ max Cg Ce * D.scalarCurvature (f 0) ^ (3 / 2 : ℝ) :=
        mul_le_mul (le_max_left _ _)
          (Real.rpow_le_rpow hQ.le hscalar (by norm_num))
          (Real.rpow_nonneg hQ.le _) (hCg.le.trans (le_max_left _ _))
  · have heq := model_scalar_evolution_eq_of_local_isometry DE D hU hf hinv hmetric hzero
    have hscale := rescaled_scalar_evolution DE hQ 0 (model_scalar_smooth DE)
    dsimp only at hevolution hscale
    rw [hscale, abs_div, abs_of_pos (sq_pos_of_pos hQ)] at hevolution
    have hbound := (div_le_iff₀ (sq_pos_of_pos hQ)).mp hevolution
    rw [heq] at hbound
    exact hbound.trans (mul_le_mul (le_max_right _ _)
      (sq_le_sq₀ hQ.le hR.le |>.mpr hscalar) (sq_nonneg _)
      (hCe.le.trans (le_max_right _ _)))

end PoincareConjecture.M45
