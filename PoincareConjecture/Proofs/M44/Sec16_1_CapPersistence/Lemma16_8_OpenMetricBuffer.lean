import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_BufferBalls










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]




theorem closure_ball_subset_preimage_of_open_metric
    (U : Opens M) (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 U)
    (hmetric : ∀ x : U, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x.1 (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v) ≤ h.inner x v v)
    (p : U) (r : ℝ) :
    closure (h.ball p r) ⊆ (Subtype.val : U → M) ⁻¹' closure (g.ball p.1 r) := by
  apply closure_minimal _ (isClosed_closure.preimage continuous_subtype_val)
  intro x hx
  exact subset_closure ((h.edist_comp_le_of_pullback_bound g contMDiff_subtype_val
    hmetric p x).trans_lt hx)




theorem isCompact_closure_ball_of_open_metric
    (U : Opens M) (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 U)
    (hmetric : ∀ x : U, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x.1 (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v) ≤ h.inner x v v)
    (p : U) (r : ℝ) (hcompact : IsCompact (closure (g.ball p.1 r)))
    (hinside : closure (g.ball p.1 r) ⊆ U) :
    IsCompact (closure (h.ball p r)) := by
  have hc : IsCompact ((Subtype.val : U → M) ⁻¹' closure (g.ball p.1 r)) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hcompact (by
      rw [Subtype.range_coe]
      exact hinside)
  exact hc.of_isClosed_subset isClosed_closure
    (closure_ball_subset_preimage_of_open_metric U g h hmetric p r)

end PoincareConjecture.M44
