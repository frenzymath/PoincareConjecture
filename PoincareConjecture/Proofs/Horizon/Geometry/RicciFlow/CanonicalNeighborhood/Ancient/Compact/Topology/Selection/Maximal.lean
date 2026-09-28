import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Closed
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.TwoCaps.Diameter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.LocalRegions
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.ChainEncounter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.CrossCores

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.CompactKappa

theorem exists_non_strong_point_threshold
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {epsilon : ℝ},
        0 < epsilon → epsilon ≤ epsilonStar → IsCompact (univ : Set M) →
        ∃ p : M, ¬ ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p := by
  classical
  obtain ⟨epsilonStar, hStar, hsmall, hclosed⟩ :=
    compact_closed_shape_of_neighborhoods P
  refine ⟨epsilonStar, hStar, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K epsilon hepsilon hε hcompact
  by_contra hnone
  have hstrong : ∀ p : M, ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p := by
    intro p
    by_contra hp
    exact hnone ⟨p, hp⟩
  obtain ⟨_, _, ⟨shape⟩⟩ := hclosed K hepsilon hε (by norm_num : (0 : ℝ) < 1)
    hcompact (fun p => Or.inl (hstrong p))
  cases shape with
  | twoCaps A B _ _ _ hA _ => exact not_le_of_gt A.one_lt_cap_constant hA
  | doubleCappedTube T _ _ _ _ hA _ => exact not_le_of_gt T.cap₁.one_lt_cap_constant hA

theorem exists_maximal_cap_with_strong_frontier_of_large_diameter_threshold
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {epsilon C : ℝ},
        0 < epsilon → epsilon ≤ epsilonStar → 0 < C →
        IsCompact (univ : Set M) →
        (∀ p : M,
          (∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p) ∨
          (∃ A : CapCertificate (K.flow.metric 0),
            A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ p ∈ A.core)) →
        (∃ p : M, twoCapDiameterConstant C *
          (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ) ≤
            metricDiameter (K.flow.metric 0) univ) →
        ∃ A : CapCertificate (K.flow.metric 0),
          A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧
          (∀ B : CapCertificate (K.flow.metric 0),
            B.epsilon = epsilon → B.cap_constant ≤ C → A.carrier ⊆ B.carrier →
              Disjoint (frontier A.carrier) B.closed_core) ∧
          (∀ x ∈ frontier A.carrier,
            ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) ∧
          (∀ x : M, x ∉ A.carrier →
            (¬ ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) →
            ∃ B : CapCertificate (K.flow.metric 0),
              B.epsilon = epsilon ∧ B.cap_constant ≤ C ∧ x ∈ B.core ∧
              Disjoint B.closed_core A.carrier ∧
              Disjoint A.closed_core B.carrier) := by
  classical
  obtain ⟨epsilon₁, h₁, hsmall, hnonneck⟩ := exists_non_strong_point_threshold P
  obtain ⟨epsilon₂, h₂, _, hmaximal⟩ :=
    ConnectedNeckCapCover.exists_maximal_cap_growth_threshold.{u}
  obtain ⟨epsilon₃, h₃, _, hclose⟩ :=
    ConnectedNeckCapCover.exists_maximal_cap_frontier_closing_threshold.{u}
  obtain ⟨epsilon₄, h₄, _, hencounter⟩ :=
    ConnectedNeckCapCover.exists_closed_core_encounter_closing_threshold.{u}
  obtain ⟨epsilon₅, h₅, _, hcross⟩ :=
    CapCertificate.exists_mutual_core_avoidance_or_closing_threshold.{u}
  refine ⟨min epsilon₁ (min epsilon₂ (min epsilon₃ (min epsilon₄ epsilon₅))),
    lt_min h₁ (lt_min h₂ (lt_min h₃ (lt_min h₄ h₅))),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K epsilon C hepsilon hε hC hcompact hcover hlarge
  have hε₁ := hε.trans (min_le_left _ _)
  have hε₂ := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₃ := hε.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hε₄ := hε.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hε₅ := hε.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  let H := strongNeckCapWholeCover K hepsilon (hε₁.trans hsmall) hC hcover
  have hnotTwo (A B : CapCertificate (K.flow.metric 0))
      (hA : A.cap_constant ≤ C) (hB : B.cap_constant ≤ C) :
      ¬ A.carrier ∪ B.carrier = univ := by
    intro hwhole
    obtain ⟨p, hp⟩ := hlarge
    exact not_lt_of_ge hp (A.metricDiameter_lt_of_two_cap_cover B
      (K.flow.connection 0) hC hA hB hwhole p)
  obtain ⟨p, hp⟩ := hnonneck K hepsilon hε₁ hcompact
  obtain ⟨A₀, hA₀, hA₀C, _⟩ := (hcover p).resolve_left hp
  obtain ⟨A, hA, _, hmax⟩ := hmaximal H hε₂ A₀ ⟨hA₀, hA₀C⟩
  obtain ⟨a, ha⟩ := A.core_nonempty
  have hmeet : (H.X ∩ A.carrier).Nonempty :=
    ⟨a, mem_univ a, A.core_subset_carrier ha⟩
  refine ⟨A, hA.1, hA.2, fun B hB hBC => hmax B ⟨hB, hBC⟩, ?_, ?_⟩
  · intro x hx
    rcases hcover x with hstrong | ⟨B, hB, hBC, hxB⟩
    · exact hstrong
    · obtain ⟨hwhole, _, _⟩ := hclose H A B hε₃ hA ⟨hB, hBC⟩ hmeet hmax
        ⟨x, hx, hxB⟩
      exact (hnotTwo A B hA.2 hBC (eq_univ_of_univ_subset hwhole)).elim
  · intro x hx hnotstrong
    obtain ⟨B, hB, hBC, hxB⟩ := (hcover x).resolve_left hnotstrong
    have hdis : Disjoint B.closed_core A.carrier := by
      by_contra hn
      obtain ⟨hwhole, _, _⟩ := hencounter H A B hε₄ hA ⟨hB, hBC⟩ hmax
        x (mem_univ x) hxB hx (not_disjoint_iff_nonempty_inter.mp hn)
      exact hnotTwo A B hA.2 hBC (eq_univ_of_univ_subset hwhole)
    refine ⟨B, hB, hBC, hxB, hdis, ?_⟩
    rcases hcross A B (hA.1.trans_le hε₅) (hB.trans hA.1.symm) hdis with
      hreverse | ⟨hwhole, _⟩
    · exact hreverse
    · exact (hnotTwo A B hA.2 hBC
        (hwhole.trans (PreconnectedSpace.connectedComponent_eq_univ A.boundary_neck.center))).elim

end PoincareConjecture.CompactKappa
