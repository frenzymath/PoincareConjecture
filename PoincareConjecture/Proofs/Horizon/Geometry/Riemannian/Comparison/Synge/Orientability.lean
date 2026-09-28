import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Synge.Isometry
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.Cover.Metric
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.Cover.Frame














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RiemannianMetric

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "OC" => Poincare.Topology.OrientationDoubleCover.TotalSpace



theorem nonempty_orientationCompatibleAtlas_of_compact_positive_sectional
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hsec : D.StrictlyPositiveSectionalCurvature) :
    Nonempty (PoincareConjecture.OrientationCompatibleAtlas M) := by
  classical
  by_contra hno
  let := Poincare.Topology.OrientationDoubleCover.chartedSpace M
  let := Poincare.Topology.OrientationDoubleCover.isManifold M
  let := Poincare.Topology.OrientationDoubleCover.t3Space M
  let := Poincare.Topology.OrientationDoubleCover.compactSpace M
  let := Poincare.Topology.OrientationDoubleCover.connectedSpace_of_not_nonempty_orientationCompatibleAtlas M hno
  let G := Poincare.Topology.OrientationDoubleCover.pullbackMetric M g
  let DG := G.leviCivitaData
  let F := Poincare.Topology.OrientationDoubleCover.flipDiffeomorph M
  have hGsec : DG.StrictlyPositiveSectionalCurvature :=
    Poincare.Topology.OrientationDoubleCover.strictlyPositiveSectionalCurvature_pullbackMetric
      M g D hsec
  have hinner : ∀ (x : OC M) (v w : TangentSpace (𝓡 3) x),
      G.inner x v w = G.inner (F x)
        (mfderiv (𝓡 3) (𝓡 3) F x v) (mfderiv (𝓡 3) (𝓡 3) F x w) := by
    intro x v w
    exact (Poincare.Topology.OrientationDoubleCover.flip_preserves_pullback_metric M g x v w).symm
  obtain ⟨p, hpos, hmin, ε, hε, γ, hgeo, hγ0, hγ1, hseg⟩ :=
    G.exists_minimum_displacement_geodesic F.continuous
      (Poincare.Topology.OrientationDoubleCover.flip_ne_self M)
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hwide : Icc (-δ) (1 + δ) ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    dsimp [δ] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ (Ioo (-ε) (1 + ε)) :=
    fun t ht => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo ht).contMDiffWithinAt
  obtain ⟨P, hi, hP, hp⟩ := ConjugateFrame.exists_orthonormal_parallel_transport G
    (show -δ < 1 + δ by linarith) isOpen_Ioo hq hwide
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc (-δ) (1 + δ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hgeo' : G.IsGeodesicOn γ (Ioo (-δ) (1 + δ)) :=
    fun t ht => hgeo t (hwide (Ioo_subset_Icc_self ht))
  have hend : γ 1 = F (γ 0) := by simpa only [hγ0] using hγ1
  have hdet : LinearMap.det (((P 1).inverse.comp
      ((mfderiv (𝓡 3) (𝓡 3) F (γ 0)).comp (P 0))).toLinearMap) < 0 := by
    exact Poincare.Topology.OrientationDoubleCover.holonomy_det_neg_of_flip_endpoint
      (M := M) zero_le_one
      (fun t ht => Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo
        (hwide (hsub ht))) hend
      (fun t ht => hi t (hsub ht)) (fun t ht u => (hP t (hsub ht) u).1)
  apply Synge.not_minimum_displacement_of_negative_holonomy DG F hinner hδ hgeo' hend
    (by simpa only [hγ0, hγ1] using hpos)
    (by simpa only [hγ0, hγ1] using hseg)
    (fun t _ u v hu hv huv => hGsec (γ t) u v hu hv huv)
    P (fun t ht => hi t (hsub ht))
    (fun t ht => hP t (Ioo_subset_Icc_self ht))
    (fun t ht => hp t (hsub ht)) hdet
  simpa only [hγ0, hγ1] using hmin

end PoincareConjecture.RiemannianMetric
