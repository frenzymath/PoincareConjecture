import PoincareConjecture.Proofs.M47.LimitCanonicalCapLocalAnalytics

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M04 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitCanonical_cap_eventually_compact_analytics
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {K : Set G.limit.sliceCarrier.carrier} (hK : IsCompact K)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in atTop,
      let f := limitCanonicalPhysicalTerminalChart G F R k
      let g := M13.scaleSmoothMetric
        ((F (G.subsequence k)).metric
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      let D := M13.scaleLeviCivitaData
        ((F (G.subsequence k)).connection
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      K ⊆ G.exhaustion.space k ∧ ∀ x ∈ K,
        ‖(D.scalarCurvature (f x), scalarGradientNorm g D (f x),
            D.laplacian D.scalarCurvature (f x) + 2 * D.ricciNormSq (f x)) -
          ((G.limit.flow.connection 0).scalarCurvature x,
            scalarGradientNorm (G.limit.flow.metric 0) (G.limit.flow.connection 0) x,
            (G.limit.flow.connection 0).laplacian
                (G.limit.flow.connection 0).scalarCurvature x +
              2 * (G.limit.flow.connection 0).ricciNormSq x)‖ ≤ eta := by
  classical
  choose W hW hbound using limitCanonical_cap_neighborhood_analytics G P F R heta
  obtain ⟨S, _hS, hcover⟩ := hK.elim_nhds_subcover W (fun x _ => hW x)
  have htail := S.eventually_all.mpr (fun x _ => hbound x)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  filter_upwards [htail, eventually_ge_atTop j] with k hk hjk
  dsimp only
  refine ⟨hj.trans (G.exhaustion.space_increasing hjk), ?_⟩
  intro x hx
  obtain ⟨q, hq, hxq⟩ : ∃ q ∈ S, x ∈ W q := by
    simpa only [mem_iUnion, exists_prop] using hcover hx
  exact hk q hq x hxq

end PoincareConjecture.M47
