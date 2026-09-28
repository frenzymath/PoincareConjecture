import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_SphereOpenMargin
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_LocalCurvatureTransport











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]




theorem sectional_lower_of_pullback_sphereJetRegion
    {sigma : UnitTwoSphere → E} (hsigma : ContMDiff (𝓡 2) (𝓡 3) ∞ sigma)
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {x : UnitTwoSphere} (hx : sigma x ∈ U) {k : ℝ}
    (hJ : (x, metricTwoJet (g.pullbackCoefficients f) (sigma x)) ∈
      sphereSectionalJetRegion sigma k)
    (u v : TangentSpace (𝓡 2) x)
    (hgram : 0 < g.inner (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u)
      (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u) *
      g.inner (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v)
        (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v) -
      (g.inner (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u)
        (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v)) ^ 2) :
    k < D.sectionalCurvature (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u)
      (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v) := by
  obtain ⟨z, hxz, hJ⟩ := hJ
  let L := mfderiv (𝓡 3) (𝓡 3) f (sigma x)
  have hcomp := mfderiv_comp x ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
    (by simp)) ((hsigma x).mdifferentiableAt (by simp))
  have hspan (w : TangentSpace (𝓡 2) x) :
      mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x w ∈ Submodule.span ℝ
        ({L (sphereCoordinateDifferential sigma z x (b 0)),
          L (sphereCoordinateDifferential sigma z x (b 1))} :
            Set (TangentSpace (𝓡 3) (f (sigma x)))) := by
    obtain ⟨a, c, hw⟩ := Submodule.mem_span_pair.mp
      (sphere_tangent_mem_coordinate_span hsigma z hxz w)
    apply Submodule.mem_span_pair.mpr
    refine ⟨a, c, ?_⟩
    rw [hcomp]
    change a • L (sphereCoordinateDifferential sigma z x (b 0)) +
      c • L (sphereCoordinateDifferential sigma z x (b 1)) =
        L (mfderiv (𝓡 2) (𝓡 3) sigma x w)
    simpa only [map_add, map_smul] using congrArg L hw
  have h := sectional_lower_of_pullback_twoJet g D hU hf hinv hx k
    (sphereCoordinateDifferential sigma z x (b 0))
    (sphereCoordinateDifferential sigma z x (b 1)) hJ
  exact sectional_lower_on_physical_plane D (f (sigma x)) h.1 h.2
    (hspan u) (hspan v) hgram



theorem sectional_lower_of_normalized_pullback_sphereJetRegion
    {sigma : UnitTwoSphere → E} (hsigma : ContMDiff (𝓡 2) (𝓡 3) ∞ sigma)
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {Q : ℝ} (hQ : 0 < Q) {x : UnitTwoSphere} (hx : sigma x ∈ U) {k : ℝ}
    (hJ : (x, metricTwoJet ((m01RescaledMetric g Q hQ).pullbackCoefficients f) (sigma x)) ∈
      sphereSectionalJetRegion sigma k)
    (u v : TangentSpace (𝓡 2) x)
    (hgram : 0 < g.inner (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u)
      (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u) *
      g.inner (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v)
        (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v) -
      (g.inner (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u)
        (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v)) ^ 2) :
    k * Q < D.sectionalCurvature (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u)
      (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v) := by
  let gQ := m01RescaledMetric g Q hQ
  let DQ := m01RescaledMetric_connection g D Q hQ
  have hgramQ : 0 < gQ.inner (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u)
      (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u) *
      gQ.inner (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v)
        (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v) -
      (gQ.inner (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u)
        (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v)) ^ 2 := by
    simp only [gQ, m01RescaledMetric_inner]
    nlinarith only [mul_pos (sq_pos_of_pos hQ) hgram]
  have h := sectional_lower_of_pullback_sphereJetRegion hsigma gQ DQ hU hf hinv hx hJ
    u v hgramQ
  have hscale := M13.homothety_sectionalCurvature_eq g gQ
    (Diffeomorph.refl (𝓡 3) M ∞) Q hQ (rescaledMetric_identity_homothety hQ)
    D DQ (f (sigma x)) (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x u)
      (mfderiv (𝓡 2) (𝓡 3) (f ∘ sigma) x v)
  simp only [Diffeomorph.coe_refl, id_eq, mfderiv_id, ContinuousLinearMap.id_apply] at hscale
  rw [hscale] at h
  exact (lt_div_iff₀ hQ).mp h

end PoincareConjecture.M44
