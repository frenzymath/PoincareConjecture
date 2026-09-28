import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundMetric
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.StereographicIntegral
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green.ChangeOfVariables









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture



theorem m60RoundSphereMetric_pullbackVolumeDensity (z : LoopPlane) :
    m60RoundSphereMetric.pullbackVolumeDensity m60SphereParameter z =
      16 / (‖z‖ ^ 2 + 4) ^ 2 := by
  unfold RiemannianMetric.pullbackVolumeDensity
  have hgram : (Matrix.of (fun i j : Fin 2 =>
      m60RoundSphereMetric.inner (m60SphereParameter z)
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z (EuclideanSpace.basisFun (Fin 2) ℝ j)))) =
      Matrix.diagonal (fun _ : Fin 2 => 16 / (‖z‖ ^ 2 + 4) ^ 2) := by
    ext i j
    simp only [Matrix.of_apply, m60RoundSphereMetric_inner, m60SphereParameter_inner,
      Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]
  rw [hgram, Matrix.det_diagonal, Fin.prod_univ_two, Real.sqrt_mul_self (by positivity)]



theorem m60RoundSphereMetric_volume_singleton (p : UnitTwoSphere) :
    m60RoundSphereMetric.volumeMeasure {p} = 0 := by
  let g := m60RoundSphereMetric
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopPlane
      (TangentSpace (𝓡 2) : UnitTwoSphere → Type) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace UnitTwoSphere := EMetricSpace.ofRiemannianMetric (𝓡 2) UnitTwoSphere
  let : NullSingletonClass (Measure.hausdorffMeasure (2 : ℝ) : Measure UnitTwoSphere) :=
    Measure.nullSingletonClass_hausdorff UnitTwoSphere (by norm_num)
  change (Measure.euclideanHausdorffMeasure 2 : Measure UnitTwoSphere) {p} = 0
  rw [Measure.euclideanHausdorffMeasure_def]
  simp



theorem m60RoundSphereMetric_integral (φ : UnitTwoSphere → ℝ) (hφ : Continuous φ) :
    (∫ p, φ p ∂m60RoundSphereMetric.volumeMeasure) =
      ∫ z : LoopPlane, φ (m60SphereParameter z) * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  have ht : m60SphereChart.target = univ := by simp [m60SphereChart]
  have hs : m60SphereChart.source = {m60SpherePole}ᶜ := by simp [m60SphereChart]
  have hnull : m60RoundSphereMetric.volumeMeasure (m60SphereChart.source)ᶜ = 0 := by
    rw [hs, compl_compl]
    exact m60RoundSphereMetric_volume_singleton _
  have hi := m60RoundSphereMetric.integral_target_eq_integral_pullback_density
    m60SphereChart.symm
    (by rw [m60SphereChart_eq_chartAt]; exact contMDiffOn_chart_symm)
    (by rw [m60SphereChart_eq_chartAt]; exact contMDiffOn_chart)
    (hφ.continuousOn)
  change (∫ p in m60SphereChart.source, φ p ∂m60RoundSphereMetric.volumeMeasure) =
    ∫ z in m60SphereChart.target, φ (m60SphereParameter z) *
      m60RoundSphereMetric.pullbackVolumeDensity m60SphereParameter z at hi
  have hae : ∀ᵐ p ∂m60RoundSphereMetric.volumeMeasure, p ∈ m60SphereChart.source := by
    rw [ae_iff]
    exact hnull
  rw [← integral_eq_setIntegral hae φ, ht,
    setIntegral_univ] at hi
  simpa only [m60RoundSphereMetric_pullbackVolumeDensity] using hi



theorem m60RoundSphereMetric_volume_univ :
    m60RoundSphereMetric.volumeMeasure.real univ = 4 * Real.pi := by
  have h := m60RoundSphereMetric_integral (fun _ => 1) continuous_const
  simpa only [integral_const, smul_eq_mul, mul_one, one_mul,
    m60SphereParameter_factor_integral] using h

end PoincareConjecture
