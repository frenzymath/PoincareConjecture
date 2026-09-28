import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Selection.StrongCollars
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Selection.ChainNoncontainment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Strong.Matching.Assembly

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.CompactKappa

theorem exists_strongDoubleCappedTube_with_cores_of_strong_collar_cover_threshold_of_m27
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (H : ConnectedNeckCapCover (K.flow.metric 0)),
        H.X = univ →
        H.necks = range (fun N : StrongEvolvingNeck K 0 H.epsilon => N.terminal_neck) →
        (∀ A ∈ H.caps, ∀ x ∈ A.carrier, x ∉ A.core →
          ∃ N : StrongEvolvingNeck K 0 H.epsilon, N.center = x) →
        H.epsilon ≤ epsilonStar → IsCompact (univ : Set M) →
        (∃ p : M, twoCapDiameterConstant H.cap_constant *
          (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ) ≤
            metricDiameter (K.flow.metric 0) univ) →
        ∃ A ∈ H.caps, ∃ B ∈ H.caps,
          ∃ S : M26StrongDoubleCappedTube K 0 H.epsilon H.cap_constant,
            S.cap₁.cap.core = A.core ∧ S.cap₂.cap.core = B.core ∧
            (∀ x : M, x ∉ S.cap₁.cap.core → x ∉ S.cap₂.cap.core →
              ∃ N : StrongEvolvingNeck K 0 H.epsilon, N.center = x) := by
  obtain ⟨epsilon₁, h₁, hsmall, hselect⟩ :=
    exists_two_maximal_caps_with_chain_core_obstruction_threshold_of_m27 P
  obtain ⟨epsilon₂, h₂, _, hnoncontainment⟩ :=
    exists_closed_core_chain_noncontainment_threshold.{u}
  obtain ⟨epsilon₃, h₃, _, hmatch⟩ :=
    exists_strongDoubleCappedTube_with_cores_of_two_caps_threshold.{u}
  refine ⟨min epsilon₁ (min epsilon₂ epsilon₃), lt_min h₁ (lt_min h₂ h₃),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K H hX hnecks hcollar hε hcompact hlarge
  have hε₁ := hε.trans (min_le_left _ _)
  have hε₂ := (hε.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hε₃ := (hε.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨A, hA, B, hB, _, _, hBA, hAB, T, hT, b, hshape, _, hremaining⟩ :=
    hselect K H hX hnecks hcollar hε₁ hcompact hlarge
  have hstrong (x : M) (hxA : x ∉ A.core) (hxB : x ∉ B.core) :
      ∃ N : StrongEvolvingNeck K 0 H.epsilon, N.center = x := by
    by_contra hn
    obtain ⟨D, hD, _, hDchain⟩ := hremaining x hxA hxB hn
    exact hnoncontainment T ((H.cap_epsilon A hA).trans_le hε₂)
      hT.quarter_capture 0 b hshape D
      ((H.cap_epsilon D hD).trans (H.cap_epsilon A hA).symm) hDchain
  obtain ⟨S, hSA, hSB, hcoverage⟩ := hmatch K A B hcompact
    (H.cap_epsilon A hA) (H.cap_epsilon B hB)
    (H.cap_constant_bound A hA) (H.cap_constant_bound B hB) hε₃ hAB hBA hstrong
  exact ⟨A, hA, B, hB, S, hSA, hSB, hcoverage⟩

end PoincareConjecture.CompactKappa
