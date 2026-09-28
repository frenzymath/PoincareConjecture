import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem limitCanonical_intrinsicEDist_univ (g : RiemannianMetric 3 M) (x y : M) :
    intrinsicEDist g univ x y = g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine le_antisymm ?_ (edist_le_intrinsicEDist univ x y)
  apply le_of_forall_gt
  intro r hr
  obtain ⟨gamma, hg0, hg1, hgamma, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hr
  have hpath : intrinsicEDist g univ x y ≤ g.pathELength gamma 0 1 :=
    sInf_le ⟨gamma, hgamma, hg0, hg1, subset_univ _, rfl⟩
  exact hpath.trans_lt hlength

theorem limitCanonical_intrinsicDiameter_univ
    [T3Space M] [ConnectedSpace M] [CompactSpace M]
    (g : RiemannianMetric 3 M) :
    intrinsicDiameter g univ ≠ ⊤ ∧
      intrinsicDiameter g univ = ENNReal.ofReal (metricDiameter g univ) ∧
      0 ≤ metricDiameter g univ := by
  let := g.toMetricSpace
  have hdist : intrinsicDiameter g univ = Metric.ediam (univ : Set M) := by
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨⟨x, y⟩, rfl⟩
      change intrinsicEDist g univ x y ≤ Metric.ediam (univ : Set M)
      rw [limitCanonical_intrinsicEDist_univ]
      exact Metric.edist_le_ediam_of_mem x.property y.property
    · apply Metric.ediam_le
      intro x hx y hy
      change g.edist x y ≤ intrinsicDiameter g univ
      rw [← limitCanonical_intrinsicEDist_univ]
      exact le_sSup ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have hfinite : intrinsicDiameter g univ ≠ ⊤ := by
    rw [hdist]
    exact isCompact_univ.isBounded.ediam_ne_top
  have hreal : (intrinsicDiameter g univ).toReal = metricDiameter g univ := by
    unfold intrinsicDiameter metricDiameter
    rw [ENNReal.toReal_sSup]
    · simp_rw [limitCanonical_intrinsicEDist_univ]
      congr 1
      ext r
      constructor
      · rintro ⟨s, ⟨p, rfl⟩, rfl⟩
        exact ⟨p, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨g.edist p.1 p.2, ⟨p, rfl⟩, rfl⟩
    · rintro r ⟨⟨x, y⟩, rfl⟩
      change intrinsicEDist g univ x y ≠ ⊤
      rw [limitCanonical_intrinsicEDist_univ]
      exact g.edist_ne_top x y
  exact ⟨hfinite, hreal ▸ (ENNReal.ofReal_toReal hfinite).symm,
    hreal ▸ ENNReal.toReal_nonneg⟩

end PoincareConjecture.M47
