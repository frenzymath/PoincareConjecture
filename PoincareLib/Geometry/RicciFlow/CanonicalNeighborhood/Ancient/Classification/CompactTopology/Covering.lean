import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.Curvature
import PoincareLib.Geometry.Riemannian.Comparison.Myers.Compact
import PoincareLib.Geometry.Riemannian.Covering.Completeness.UniversalCover
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryRicci
import PoincareLib.Geometry.Riemannian.Connection.Construction

/-!
# Compact covers of compact positive-curvature manifolds

The uniform positive Ricci bound lifts to every Riemannian covering. Arbitrary
covering completeness and Bonnet--Myers then make each connected cover compact.
In particular the fundamental group of a compact positive-sectional-curvature
three-manifold is finite.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) E]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ E]
  [T3Space M] [T3Space E] [CompactSpace M] [PreconnectedSpace E]

/-- Every connected Riemannian cover of a complete compact manifold with
strictly positive sectional curvature is compact. -/
theorem compactSpace_covering_of_compact_positive_sectional
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (h : RiemannianMetric n E) (Dh : LeviCivitaData h) (hn : 2 ≤ n)
    (hc : MetricComplete g)
    (hsec : ∀ x u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v)
    (q : E → M) (hq : ContMDiff (𝓡 n) (𝓡 n) ∞ q) (hcover : IsCoveringMap q)
    (hmetric : ∀ x u v, h.inner x u v = g.inner (q x)
      (mfderiv (𝓡 n) (𝓡 n) q x u) (mfderiv (𝓡 n) (𝓡 n) q x v)) :
    CompactSpace E := by
  obtain ⟨k, hk, hRic⟩ := D.exists_pos_ricci_lower_bound_of_compact_positive_sectional hn hsec
  apply h.compactSpace_of_positive_ricci Dh
    (h.metricComplete_of_isCoveringMap g hq hcover hmetric hc) hk
  intro x v
  rw [Dh.ricci_eq_of_local_isometry D isOpen_univ hq.contMDiffOn
    (fun y _ u v => hmetric y u v) (mem_univ x), hmetric]
  exact hRic _ _

/-- Covering fibers are finite under the same positive-curvature hypotheses. -/
theorem finite_covering_fiber_of_compact_positive_sectional
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (h : RiemannianMetric n E) (Dh : LeviCivitaData h) (hn : 2 ≤ n)
    (hc : MetricComplete g)
    (hsec : ∀ x u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v)
    (q : E → M) (hq : ContMDiff (𝓡 n) (𝓡 n) ∞ q) (hcover : IsCoveringMap q)
    (hmetric : ∀ x u v, h.inner x u v = g.inner (q x)
      (mfderiv (𝓡 n) (𝓡 n) q x u) (mfderiv (𝓡 n) (𝓡 n) q x v)) (x : M) :
    Finite (q ⁻¹' {x}) := by
  let : CompactSpace E := g.compactSpace_covering_of_compact_positive_sectional D h Dh
    hn hc hsec q hq hcover hmetric
  let : DiscreteTopology (q ⁻¹' {x}) := (hcover x).discreteTopology_fiber
  let : CompactSpace (q ⁻¹' {x}) :=
    isCompact_iff_compactSpace.mp (isClosed_singleton.preimage hq.continuous).isCompact
  exact finite_of_compact_of_discrete

end PoincareMT.RiemannianMetric

namespace Poincare.Topology.UniversalCover

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [CompactSpace M] [ConnectedSpace M]

/-- The canonical universal cover of a complete compact positive-sectional-
curvature three-manifold is compact. -/
theorem compactSpace_of_positive_sectional
    (g : PoincareMT.RiemannianMetric 3 M) (D : PoincareMT.LeviCivitaData g)
    (hc : PoincareMT.MetricComplete g)
    (hsec : ∀ x u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) (x₀ : M) :
    CompactSpace (UniversalCover x₀) := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let : SemilocallySimplyConnectedSpace M :=
    semilocallySimplyConnectedSpace_of_chartedSpace 3 M
  let := chartedSpace x₀
  let := isManifold x₀
  let := t3Space x₀
  let q := proj (x₀ := x₀)
  let hq := isLocalDiffeomorph x₀
  let h := g.pullbackOfLocalDiffeomorph q hq
  exact g.compactSpace_covering_of_compact_positive_sectional D h h.leviCivitaData
    (by norm_num) hc hsec q hq.contMDiff (isCoveringMap x₀) (fun _ _ _ => rfl)

/-- A compact positive-sectional-curvature three-manifold has finite
fundamental group, using the literal path-class model of its universal cover. -/
theorem finite_fundamentalGroup_of_positive_sectional
    (g : PoincareMT.RiemannianMetric 3 M) (D : PoincareMT.LeviCivitaData g)
    (hc : PoincareMT.MetricComplete g)
    (hsec : ∀ x u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) (x₀ : M) :
    Finite (FundamentalGroup M x₀) := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let : SemilocallySimplyConnectedSpace M :=
    semilocallySimplyConnectedSpace_of_chartedSpace 3 M
  let : CompactSpace (UniversalCover x₀) := compactSpace_of_positive_sectional g D hc hsec x₀
  let : CompactSpace (proj (x₀ := x₀) ⁻¹' {x₀}) :=
    isCompact_iff_compactSpace.mp
      (isClosed_singleton.preimage (continuous_proj x₀)).isCompact
  let : Finite (proj (x₀ := x₀) ⁻¹' {x₀}) := finite_of_compact_of_discrete
  apply Finite.of_injective
    (fun p : FundamentalGroup M x₀ =>
      (⟨⟨x₀, p⟩, rfl⟩ : proj (x₀ := x₀) ⁻¹' {x₀}))
  intro a b h
  have hab := congrArg Subtype.val h
  injection hab

end Poincare.Topology.UniversalCover
