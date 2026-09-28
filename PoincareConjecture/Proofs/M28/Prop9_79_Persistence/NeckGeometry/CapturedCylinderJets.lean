import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.CapturedCylinderChart
import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.MetricTransition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.Proofs.M28.NeckTransfer

open PoincareConjecture.M28.tube FiniteHessian

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem capturedCylinderCoordinates_atlas_regular
    {X : Type v} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    {h : RiemannianMetric 3 X} (gX : RiemannianMetric 3 X)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) (s : ℝ) (p : M)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ capturedCylinderChartDomain e N q s p) :
    ContDiffAt ℝ ∞ (gX.pullbackCoefficients (e ∘ (extChartAt (𝓡 3) p).symm))
        (capturedCylinderCoordinates e N q s p x) ∧
      (gX.pullbackCoefficients (e ∘ (extChartAt (𝓡 3) p).symm)
        (capturedCylinderCoordinates e N q s p x)).IsInvertible := by
  let c := extChartAt (𝓡 3) p
  let y := capturedCylinderCoordinates e N q s p x
  have hy : y ∈ c.target := c.map_source hx.2
  have hs : c.symm y ∈ e.source := by
    rw [show c.symm y = capturedCylinderMap e N q s x from c.left_inv hx.2]
    exact capturedCylinderMap_mem_source e N hcapture q s hx.1
  have hcinv : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have he := e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds hs)
  refine ⟨gX.contDiffAt_pullbackCoefficients (he.comp y hcinv), ?_⟩
  apply gX.isInvertible_pullbackCoefficients
  rw [mfderiv_comp y (he.mdifferentiableAt (by simp))
    (hcinv.mdifferentiableAt (by simp))]
  have helocal : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ e (c.symm y) :=
    ⟨e, hs, fun _ _ => rfl⟩
  have heinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) e (c.symm y)) :=
    (helocal.mfderivToContinuousLinearEquiv (by simp)).injective
  have hi := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 3) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
  exact heinj.comp hi.injective

theorem hasUniformJetBoundsAt_capturedCylinderCoordinates_fderiv
    {ι : Type*} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
    [∀ i, IsManifold (𝓡 3) ∞ (X i)]
    {h : ∀ i, RiemannianMetric 3 (X i)} (gX : ∀ i, RiemannianMetric 3 (X i))
    (e : ∀ i, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X i) ∞)
    (N : ∀ i, EpsilonNeck (h i)) (hcapture : ∀ i, (N i).carrier ⊆ (e i).target)
    (q : ι → UnitTwoSphere) (s : ι → ℝ) (p : ι → M)
    (hs : ∀ i, s i ∈ Ioo (-(N i).epsilon⁻¹) (N i).epsilon⁻¹)
    (hp : ∀ i, (e i).symm ((N i).coordinate_map (q i, s i)) ∈
      (extChartAt (𝓡 3) (p i)).source) (n : ℕ)
    (hAj : HasUniformJetBoundsAt (n + 1)
      (fun i => (gX i).pullbackCoefficients (cylinderNeckChart (N i) (q i) (s i)))
      (fun _ => 0))
    (hBj : HasUniformJetBoundsAt (n + 1)
      (fun i => (gX i).pullbackCoefficients ((e i) ∘ (extChartAt (𝓡 3) (p i)).symm))
      (fun i => capturedCylinderCoordinates (e i) (N i) (q i) (s i) (p i) 0))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hAe : ∀ i v, a * ‖v‖ ^ 2 ≤
      (gX i).pullbackCoefficients (cylinderNeckChart (N i) (q i) (s i)) 0 v v)
    (hBe : ∀ i v, b * ‖v‖ ^ 2 ≤
      (gX i).pullbackCoefficients ((e i) ∘ (extChartAt (𝓡 3) (p i)).symm)
        (capturedCylinderCoordinates (e i) (N i) (q i) (s i) (p i) 0) v v) :
    HasUniformJetBoundsAt (n + 1)
      (fun i => fderiv ℝ (capturedCylinderCoordinates (e i) (N i) (q i) (s i) (p i)))
      (fun _ => 0) := by
  refine hasUniformJetBoundsAt_fderiv_of_metric_pullback n
    (U := fun i => capturedCylinderChartDomain (e i) (N i) (q i) (s i) (p i))
    (fun i => isOpen_capturedCylinderChartDomain (e i) (N i) (hcapture i) (q i) (s i) (p i))
    (fun i => zero_mem_capturedCylinderChartDomain (e i) (N i) (q i) (hs i) (p i) (hp i))
    (fun i => contDiffOn_capturedCylinderCoordinates
      (e i) (N i) (hcapture i) (q i) (s i) (p i))
    ?_ ?_ ?_ ?_ ?_ ?_ hAj hBj ha hb hAe hBe
  · intro i y hy
    exact ((gX i).contDiffAt_pullbackCoefficients
      ((contMDiffOn_cylinderNeckChart (N i) (q i) (s i)).contMDiffAt
        ((isOpen_cylinderNeckChartDomain (N i) (q i) (s i)).mem_nhds hy.1))).contDiffWithinAt
  · intro i y hy
    exact (capturedCylinderCoordinates_atlas_regular
      (gX i) (e i) (N i) (hcapture i) (q i) (s i) (p i) hy).1
  · intro i y hy
    exact (gX i).isInvertible_pullbackCoefficients
      (cylinderNeckChart_mfderiv_isInvertible (N i) (q i) (s i) hy.1).injective
  · intro i y hy
    exact (capturedCylinderCoordinates_atlas_regular
      (gX i) (e i) (N i) (hcapture i) (q i) (s i) (p i) hy).2
  · intro i y _ v w
    exact (gX i).symm _ _ _
  · intro i y hy v w
    exact congrArg (fun B : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => B v w)
      (capturedCylinderCoordinates_source_coefficients
        (gX i) (e i) (N i) (hcapture i) (q i) (s i) (p i) hy)

end PoincareConjecture.Proofs.M28.NeckTransfer
