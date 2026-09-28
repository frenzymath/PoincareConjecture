import PoincareConjecture.Proofs.M47.LimitCanonicalNeckComparison
import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckImage










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem limitCanonical_eventually_neck_image
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (N : EpsilonNeck (G.limit.flow.metric 0))
    (hconnection : N.connection = G.limit.flow.connection 0)
    {K : Set G.limit.sliceCarrier.carrier} (hK : IsCompact K) (hNK : N.carrier ⊆ K) :
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
      K ⊆ G.exhaustion.space k ∧ ∃ Eimage : EpsilonNeck g,
        Eimage.epsilon = N.epsilon ∧ Eimage.center = f N.center ∧ Eimage.connection = D ∧
        Eimage.carrier = f '' N.carrier ∧ Eimage.central_sphere = f '' N.central_sphere ∧
        Eimage.coordinate_map = f ∘ N.coordinate_map ∧
        Eimage.coordinate_inverse = N.coordinate_inverse ∘ f.symm ∧
        ∀ a b : ℝ, -N.epsilon⁻¹ ≤ a → b ≤ N.epsilon⁻¹ →
          Eimage.region a b = f '' N.region a b := by
  filter_upwards [limitCanonical_eventually_neck_normalized_comparison
    G P F R N hconnection hK hNK] with k hk
  dsimp only
  refine ⟨hk.1, exists_cap_neck_image_of_normalized_comparison N
    (M13.scaleLeviCivitaData
      ((F (G.subsequence k)).connection
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
      (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k)))
    (limitCanonicalPhysicalTerminalChart G F R k) ?_ hk.2.1 hk.2.2⟩
  rw [limitCanonicalPhysicalTerminalChart, limitCanonicalPhysicalChart_source]
  exact hNK.trans hk.1

end PoincareConjecture.M47
