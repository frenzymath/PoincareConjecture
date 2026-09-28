import PoincareConjecture.Proofs.M47.LimitCanonicalComponentLocalCurvature
import PoincareConjecture.Proofs.M47.LimitCanonicalComponentImage









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




theorem limitCanonical_component_eventually_physical_curvature
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier))
    (a : ℝ) (hsec : ∀ x : G.limit.sliceCarrier.carrier,
      ∀ u v : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (G.limit.flow.metric 0) x u v →
          a < (G.limit.flow.connection 0).sectionalCurvature x u v)
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
      G.exhaustion.space k = univ ∧
        f.target = connectedComponent (f G.limit.base) ∧
        ∀ x : G.limit.sliceCarrier.carrier,
          (∀ u v : TangentSpace (𝓡 3) (f x),
            a * metricGram g (f x) u v ≤ D.curvatureTensor (f x) u v u v) ∧
          6 * a ≤ D.scalarCurvature (f x) ∧
          |D.scalarCurvature (f x) - (G.limit.flow.connection 0).scalarCurvature x| < eta := by
  classical
  let : CompactSpace G.limit.sliceCarrier.carrier := isCompact_univ_iff.mp hcompact
  choose W hW hbound using
    limitCanonical_component_neighborhood_curvature G P F R a hsec heta
  obtain ⟨S, _hS, hcover⟩ := isCompact_univ.elim_nhds_subcover W (fun x _ => hW x)
  have htail := (S.eventually_all).mpr (fun x _ => hbound x)
  filter_upwards [htail, limitCanonical_eventually_physical_component_image G F R hcompact]
    with k hk hfull
  dsimp only
  refine ⟨hfull.1, hfull.2 0
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
    (limitCanonical_terminal_clock_mem G k), ?_⟩
  intro x
  obtain ⟨q, hq, hx⟩ : ∃ q ∈ S, x ∈ W q := by
    simpa only [mem_iUnion, exists_prop] using hcover (mem_univ x)
  exact hk q hq x hx

end PoincareConjecture.M47
