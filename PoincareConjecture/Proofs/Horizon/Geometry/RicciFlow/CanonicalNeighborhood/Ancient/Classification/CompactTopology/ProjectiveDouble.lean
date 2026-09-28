import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.Covering
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.ProjectiveDouble.Infinite

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [CompactSpace M] [ConnectedSpace M]

theorem not_nonempty_smoothProjectiveDoubleModel_of_compact_positive_sectional
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) :
    ¬ Nonempty (SmoothProjectiveDoubleModel M) := by
  rintro ⟨C⟩
  obtain ⟨b, hinfinite⟩ := C.exists_infinite_fundamentalGroup
  let : Finite (FundamentalGroup M b) :=
    Poincare.Topology.UniversalCover.finite_fundamentalGroup_of_positive_sectional
      g D hc hsec b
  exact hinfinite.false

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.ClosedComponentCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [CompactSpace M] [ConnectedSpace M]

theorem not_univ_of_projectiveDouble_of_compact_positive_sectional
    {Y : Set M} (C : ClosedComponentCertificate .realProjectiveThreeConnectedSum Y)
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) : Y ≠ univ := by
  intro hY
  subst Y
  let S := C.smooth_model
  let := S.model_topology
  let := S.model_charted
  let := S.model_manifold
  obtain ⟨P⟩ := S.standard_smooth
  let e : S.model ≃ₜ M := {
    toFun := S.forward
    invFun := S.inverse
    left_inv := S.right_inverse
    right_inv := fun x => S.left_inverse x (mem_univ x)
    continuous_toFun := S.forward_smooth.continuous
    continuous_invFun := continuousOn_univ.mp S.inverse_smooth.continuousOn }
  obtain ⟨b, hinfinite⟩ := P.exists_infinite_fundamentalGroup
  let : Finite (FundamentalGroup M (e b)) :=
    Poincare.Topology.UniversalCover.finite_fundamentalGroup_of_positive_sectional
      g D hc hsec (e b)
  let : Finite (FundamentalGroup S.model b) :=
    Finite.of_injective (e.fundamentalGroupMulEquiv b) (e.fundamentalGroupMulEquiv b).injective
  exact hinfinite.false

end PoincareConjecture.ClosedComponentCertificate
