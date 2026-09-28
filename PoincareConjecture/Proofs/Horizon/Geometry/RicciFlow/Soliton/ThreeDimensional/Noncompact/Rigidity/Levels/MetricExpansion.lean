import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.TangentialTrace
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Regularity.Potential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.MetricExpansion.Manifold









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open Poincare.Geometry.Riemannian.Convexity
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private theorem ricci_smul_self (D : LeviCivitaData g)
    (x : M) (c : ℝ) (v : TangentSpace (𝓡 3) x) :
    D.ricci x (c • v) (c • v) = c ^ 2 * D.ricci x v v := by
  unfold ricci
  simp_rw [← D.curvatureTensor_bilinear_first_third_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring



theorem ricci_le_half_scalarCurvature_mul_inner_of_sectional_nonneg
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ v w : TangentSpace (𝓡 3) x, 0 ≤ D.sectionalCurvature x v w)
    (v : TangentSpace (𝓡 3) x) :
    D.ricci x v v ≤ D.scalarCurvature x / 2 * g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_cases hv : v = 0
  · simp [hv, ricci, ← D.curvatureTensor_bilinear_first_third_apply]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : g.inner x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = 1 := by
    change inner ℝ (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = 1
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h := D.two_mul_ricci_unit_le_scalarCurvature_add x 0 (by norm_num)
    (by simpa using hsec) (‖v‖⁻¹ • v) hunit
  rw [ricci_smul_self] at h
  simp only [mul_zero, add_zero] at h
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg ‖v‖)
  have hcancel : ‖v‖ ^ 2 * (2 * (‖v‖⁻¹ ^ 2 * D.ricci x v v)) =
      2 * D.ricci x v v := by field_simp
  rw [hcancel] at hh
  change D.ricci x v v ≤ D.scalarCurvature x / 2 * inner ℝ v v
  rw [real_inner_self_eq_norm_sq]
  nlinarith

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem hessian_ge_one_sub_scalar_half
    (S : GradientShrinkingSolitonData 3 M)
    (x : M) (v : TangentSpace (𝓡 3) x) :
    ((1 - S.connection.scalarCurvature x) / 2) * S.metric.inner x v v ≤
      S.connection.hessian S.potential x v v := by
  have hric := S.connection.ricci_le_half_scalarCurvature_mul_inner_of_sectional_nonneg x
    (fun v w ↦ S.connection.sectionalCurvature_nonneg_of_nonnegative_curvatureOperator
      x (S.nonnegative_curvature x) v w) v
  have heq := S.soliton_equation x v v
  nlinarith



theorem hessian_nonneg_of_scalarCurvature_le_one
    (S : GradientShrinkingSolitonData 3 M)
    (x : M)
    (hR : S.connection.scalarCurvature x ≤ 1) (v : TangentSpace (𝓡 3) x) :
    0 ≤ S.connection.hessian S.potential x v v := by
  have hinner : 0 ≤ S.metric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (S.metric.pos x v hv).le
  exact (mul_nonneg (div_nonneg (sub_nonneg.mpr hR) (by norm_num)) hinner).trans
    (S.hessian_ge_one_sub_scalar_half x v)




theorem exists_local_normalizedGradient_flow_with_nondecreasing_metric
    (S : GradientShrinkingSolitonData 3 M) {U : Set M}
    (hU : IsOpen U)
    (hregular : ∀ y ∈ U, 0 < S.metric.inner y
      (S.connection.gradient S.potential y) (S.connection.gradient S.potential y))
    (hR : ∀ y ∈ U, S.connection.scalarCurvature y ≤ 1)
    {x : M} (hx : x ∈ U) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ Φ (Ioo (-δ) δ ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      (∀ y ∈ V, (∀ t ∈ Ioo (-δ) δ, Φ (t, y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 3) (fun t => Φ (t, y))
          (S.connection.normalizedGradient S.potential) (Ioo (-δ) δ)) ∧
      ∀ y ∈ V, ∀ t ∈ Ico 0 δ,
        S.potential (Φ (t, y)) = S.potential y + t ∧
        ∀ v : TangentSpace (𝓡 3) y, mvfderiv (𝓡 3) S.potential y v = 0 →
          S.metric.inner y v v ≤ S.metric.inner (Φ (t, y))
            (mfderiv (𝓡 3) (𝓡 3) (fun z => Φ (t, z)) y v)
            (mfderiv (𝓡 3) (𝓡 3) (fun z => Φ (t, z)) y v) :=
  S.connection.exists_local_normalizedGradient_manifoldFlow_with_nondecreasing_metric
    hU S.potential_contMDiff.contMDiffOn hregular
    (fun y hy v _ => S.hessian_nonneg_of_scalarCurvature_le_one y (hR y hy) v) hx

end PoincareConjecture.GradientShrinkingSolitonData
