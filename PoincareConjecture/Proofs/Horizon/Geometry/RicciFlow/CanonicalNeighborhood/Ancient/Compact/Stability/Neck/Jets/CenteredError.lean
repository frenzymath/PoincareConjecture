import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Neck.CenteredNeckMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.ParametrizedCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M]

theorem centeredCylinderMetric_scalar_pullback
    (g : RiemannianMetric 3 M) (Φ : RoundCylinderSpace → M)
    (c : ℝ) (theta : UnitTwoSphere) (s : ℝ) {p : E}
    (hΦ : MDifferentiableAt IC (𝓡 3) Φ (centeredCylinderLift theta s p)) :
    centeredCylinderMetric (fun z v w => c * roundCylinderPullback g Φ z v w)
      theta s p = c • g.parametrizedCoefficients (Φ ∘ centeredCylinderLift theta s) p := by
  have hd := mfderiv_comp p hΦ
    ((centeredCylinderLift_contMDiff theta s p).mdifferentiableAt (by simp))
  have hdv (v : E) : mfderiv (𝓡 3) (𝓡 3) (Φ ∘ centeredCylinderLift theta s) p v =
      mfderiv IC (𝓡 3) Φ (centeredCylinderLift theta s p)
        (mfderiv (𝓡 3) IC (centeredCylinderLift theta s) p v) :=
    congrArg (fun D => D v) hd
  apply euclideanThree_bilinear_ext
  intro i j
  rw [centeredCylinderMetric, centeredCylinderBilinear_basis]
  have hcoord : cylinderEuclideanEquiv p + (0, s) =
      (cylinderHorizontalProjection p, cylinderHeightCovector p + s) := by
    apply Prod.ext
    · exact add_zero _
    · rfl
  rw [hcoord]
  have hP (k : Fin 3) : cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      (roundCylinderCoordinateBasis k).1 :=
    congrArg Prod.fst (cylinderEuclideanEquiv_basis k)
  simp only [smul_apply, smul_eq_mul,
    RiemannianMetric.parametrizedCoefficients_apply, hdv,
    centeredCylinderLift_mfderiv, hP, cylinderHeightCovector_basis]
  rfl

theorem centeredCylinderMetric_scalar_pullback_germ
    (g : RiemannianMetric 3 M) (Φ : RoundCylinderSpace → M)
    (c : ℝ) (theta : UnitTwoSphere) (s : ℝ)
    {U : Set RoundCylinderSpace} (hU : IsOpen U) (hz : (theta, s) ∈ U)
    (hΦ : ContMDiffOn IC (𝓡 3) ∞ Φ U) :
    centeredCylinderMetric (fun z v w => c * roundCylinderPullback g Φ z v w) theta s
      =ᶠ[𝓝 (0 : E)] fun p =>
        c • g.parametrizedCoefficients (Φ ∘ centeredCylinderLift theta s) p := by
  have hzero : centeredCylinderLift theta s 0 ∈ U := by
    simpa only [centeredCylinderLift_zero] using hz
  filter_upwards [((centeredCylinderLift_contMDiff theta s).continuous.continuousAt).preimage_mem_nhds
    (hU.mem_nhds hzero)] with p hp
  exact centeredCylinderMetric_scalar_pullback g Φ c theta s
    ((hΦ.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))

theorem centeredCylinderError_difference_jet_eq
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M']
    [IsManifold (𝓡 3) ∞ M']
    (g : RiemannianMetric 3 M) (g' : RiemannianMetric 3 M')
    (Φ : RoundCylinderSpace → M) (Φ' : RoundCylinderSpace → M')
    (c c' : ℝ) (theta : UnitTwoSphere) (s : ℝ)
    {U : Set RoundCylinderSpace} (hU : IsOpen U) (hz : (theta, s) ∈ U)
    (hΦ : ContMDiffOn IC (𝓡 3) ∞ Φ U)
    (hΦ' : ContMDiffOn IC (𝓡 3) ∞ Φ' U) (j : ℕ) :
    iteratedFDeriv ℝ j (fun p =>
      centeredCylinderError (fun z v w => c * roundCylinderPullback g Φ z v w) theta s p -
      centeredCylinderError (fun z v w => c' * roundCylinderPullback g' Φ' z v w) theta s p) 0 =
    iteratedFDeriv ℝ j (fun p =>
      c • g.parametrizedCoefficients (Φ ∘ centeredCylinderLift theta s) p -
      c' • g'.parametrizedCoefficients (Φ' ∘ centeredCylinderLift theta s) p) 0 := by
  suffices he : (fun p =>
      centeredCylinderError (fun z v w => c * roundCylinderPullback g Φ z v w) theta s p -
      centeredCylinderError (fun z v w => c' * roundCylinderPullback g' Φ' z v w) theta s p)
      =ᶠ[𝓝 (0 : E)] (fun p =>
        c • g.parametrizedCoefficients (Φ ∘ centeredCylinderLift theta s) p -
        c' • g'.parametrizedCoefficients (Φ' ∘ centeredCylinderLift theta s) p) from
    (he.iteratedFDeriv ℝ j).self_of_nhds
  filter_upwards [centeredCylinderMetric_scalar_pullback_germ g Φ c theta s hU hz hΦ,
    centeredCylinderMetric_scalar_pullback_germ g' Φ' c' theta s hU hz hΦ'] with p hp hp'
  rw [← centeredCylinderMetric_sub_model, ← centeredCylinderMetric_sub_model]
  simp only
  rw [hp, hp']
  abel

end PoincareConjecture.MetricSurgery
