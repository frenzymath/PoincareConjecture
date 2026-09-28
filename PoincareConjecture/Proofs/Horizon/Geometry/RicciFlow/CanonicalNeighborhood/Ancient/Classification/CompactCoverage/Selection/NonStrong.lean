import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Cover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Global
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.Positivity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.SphereBundle













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.CompactKappa



theorem exists_non_strong_point_threshold_of_m27
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {epsilon : ℝ},
        0 < epsilon → epsilon ≤ epsilonStar → IsCompact (univ : Set M) →
        ∃ p : M, ¬ ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p := by
  classical
  obtain ⟨epsilonStar, hStar, hsmall, hglobal⟩ := P.global_neck_cap
  refine ⟨epsilonStar, hStar, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K epsilon hepsilon hε hcompact
  by_contra hnone
  have hstrong : ∀ p : M, ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p := by
    intro p
    by_contra hp
    exact hnone ⟨p, hp⟩
  let H := strongNeckCapWholeCover K hepsilon (hε.trans hsmall)
    (by norm_num : (0 : ℝ) < 1) (fun p => Or.inl (hstrong p))
  obtain ⟨conclusion⟩ := hglobal (K.flow.metric 0) H hε rfl
  rcases conclusion.closed_or_fibration_of_isCompact hcompact with hclosed | hfibration
  · obtain ⟨_, _, ⟨shape⟩⟩ := hclosed
    cases shape with
    | twoCaps A B _ _ _ hA _ => exact not_le_of_gt A.one_lt_cap_constant hA
    | doubleCappedTube T _ _ _ _ hA _ => exact not_le_of_gt T.cap₁.one_lt_cap_constant hA
  · obtain ⟨T, _, hwhole⟩ := hfibration
    let : CompactSpace M := ⟨hcompact⟩
    exact T.not_whole_of_compact_positive_sectional (K.flow.connection 0)
      (K.complete 0 le_rfl)
      (K.positiveSectionalCurvature_of_compact P.classificationServices hcompact 0 le_rfl)
      hwhole

end PoincareConjecture.CompactKappa
