import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Selection.NonStrong
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Selection.Encounter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.FiniteChain

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.CompactKappa

theorem exists_two_maximal_caps_with_chain_core_obstruction_threshold_of_m27
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
          (∀ D ∈ H.caps, A.carrier ⊆ D.carrier →
            Disjoint (frontier A.carrier) D.closed_core) ∧
          (∀ D ∈ H.caps, B.carrier ⊆ D.carrier →
            Disjoint (frontier B.carrier) D.closed_core) ∧
          Disjoint B.closed_core A.carrier ∧ Disjoint A.closed_core B.carrier ∧
          ∃ T : BalancedNeckChain (K.flow.metric 0) A.epsilon,
            A.IsOutgoingChain H T ∧ ∃ b : ℤ, T.shape = .finite 0 b ∧
              A.carrier ∪ (T.unionOpen : Set M) ∪ B.carrier = univ ∧
              ∀ x : M, x ∉ A.core → x ∉ B.core →
                (¬ ∃ N : StrongEvolvingNeck K 0 H.epsilon, N.center = x) →
                ∃ D ∈ H.caps, x ∈ D.core ∧ D.closed_core ⊆ (T.unionOpen : Set M) := by
  classical
  obtain ⟨epsilon₁, h₁, hsmall, hchain⟩ :=
    exists_outgoing_chain_with_neck_free_frontier_threshold.{u}
  obtain ⟨epsilon₂, h₂, _, hnonneck⟩ := exists_non_strong_point_threshold_of_m27 P
  obtain ⟨epsilon₃, h₃, _, hmaximal⟩ :=
    ConnectedNeckCapCover.exists_maximal_cap_growth_threshold.{u}
  obtain ⟨epsilon₄, h₄, _, hcapped⟩ :=
    CapCertificate.exists_outgoing_capped_tube_threshold.{u}
  obtain ⟨epsilon₅, h₅, _, hfrontier⟩ :=
    CapCertificate.exists_chain_frontier_positive_end_threshold.{u}
  obtain ⟨epsilon₆, h₆, _, hencounter⟩ :=
    ConnectedNeckCapCover.exists_closed_core_encounter_closing_threshold.{u}
  obtain ⟨epsilon₇, h₇, _, hclose⟩ :=
    CapCertificate.exists_finite_chain_closing_threshold.{u}
  let epsilonStar := min epsilon₁
    (min epsilon₂ (min epsilon₃ (min epsilon₄ (min epsilon₅ (min epsilon₆ epsilon₇)))))
  refine ⟨epsilonStar,
    lt_min h₁ (lt_min h₂ (lt_min h₃ (lt_min h₄ (lt_min h₅ (lt_min h₆ h₇))))),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K H hX hnecks hcollar hε hcompact hlarge
  have hthresholds : H.epsilon ≤ epsilon₁ ∧ H.epsilon ≤ epsilon₂ ∧
      H.epsilon ≤ epsilon₃ ∧ H.epsilon ≤ epsilon₄ ∧ H.epsilon ≤ epsilon₅ ∧
      H.epsilon ≤ epsilon₆ ∧ H.epsilon ≤ epsilon₇ := by
    simpa only [epsilonStar, le_min_iff] using hε
  obtain ⟨hε₁, hε₂, hε₃, hε₄, hε₅, hε₆, hε₇⟩ := hthresholds
  have hcover (x : M) :
      (∃ N : StrongEvolvingNeck K 0 H.epsilon, N.center = x) ∨
        (∃ A ∈ H.caps, x ∈ A.core) := by
    rcases H.pointwise_cover x (by rw [hX]; exact mem_univ x) with
      ⟨N, hN, hcenter⟩ | hcap
    · rw [hnecks] at hN
      obtain ⟨S, rfl⟩ := hN
      exact Or.inl ⟨S, S.terminal_center.symm.trans hcenter⟩
    · exact Or.inr hcap
  have hnotTwo (A B : CapCertificate (K.flow.metric 0)) (hA : A ∈ H.caps)
      (hB : B ∈ H.caps) : ¬ A.carrier ∪ B.carrier = univ := by
    intro hwhole
    obtain ⟨p, hp⟩ := hlarge
    exact not_lt_of_ge hp (A.metricDiameter_lt_of_two_cap_cover B
      (K.flow.connection 0) H.cap_constant_pos (H.cap_constant_bound A hA)
      (H.cap_constant_bound B hB) hwhole p)
  have havoid (A D : CapCertificate (K.flow.metric 0)) (hA : A ∈ H.caps)
      (hD : D ∈ H.caps)
      (hmax : ∀ B ∈ H.caps, A.carrier ⊆ B.carrier →
        Disjoint (frontier A.carrier) B.closed_core)
      (x : M) (hxD : x ∈ D.core) (hxA : x ∉ A.carrier) :
      Disjoint D.closed_core A.carrier := by
    by_contra hn
    obtain ⟨hwhole, _, _⟩ := hencounter H A D hε₆ hA hD hmax
      x (by rw [hX]; exact mem_univ x) hxD hxA
      (not_disjoint_iff_nonempty_inter.mp hn)
    exact hnotTwo A D hA hD
      (eq_univ_of_univ_subset (by simpa only [hX] using hwhole))
  obtain ⟨p, hp⟩ := hnonneck K H.epsilon_pos hε₂ hcompact
  obtain ⟨A₀, hA₀, hpA₀⟩ := (hcover p).resolve_left hp
  obtain ⟨A, hA, hA₀A, hmaxA⟩ := hmaximal H hε₃ A₀ hA₀
  have hpA : p ∈ A.core := by
    by_contra hn
    exact hp (hcollar A hA p (hA₀A (A₀.core_subset_carrier hpA₀)) hn)
  obtain ⟨T, hT, hfree⟩ := hchain H hε₁ A hA
  obtain ⟨tube, _, _, _, hcarrier⟩ := hcapped A
    ((H.cap_epsilon A hA).trans_le hε₄) H T hT
  have hproper : A.carrier ∪ (T.unionOpen : Set M) ≠ univ := by
    intro hwhole
    exact tube.not_isCompact_carrier ((hcarrier.trans hwhole).symm ▸ hcompact)
  have hnonempty : (A.carrier ∪ (T.unionOpen : Set M)).Nonempty :=
    ⟨p, Or.inl (A.core_subset_carrier hpA)⟩
  have hfrontnonempty : (frontier (A.carrier ∪ (T.unionOpen : Set M))).Nonempty := by
    by_contra hn
    rcases frontier_eq_empty_iff.mp (not_nonempty_iff_eq_empty.mp hn) with hempty | hwhole
    · exact hnonempty.ne_empty hempty
    · exact hproper hwhole
  obtain ⟨y, hy⟩ := hfrontnonempty
  obtain ⟨b, hb, hnext, _⟩ := hfrontier A ((H.cap_epsilon A hA).trans_le hε₅)
    T hT.zero_active hT.nonnegative hT.first_neck hT.quarter_capture y hy
  have hshape := hT.shape_eq_finite_of_right_endpoint hb hnext
  have hyA : y ∉ A.carrier := by
    intro hyA
    exact ((A.carrier_open.union T.unionOpen.isOpen).frontier_eq ▸ hy).2 (Or.inl hyA)
  have hynon : ¬ ∃ N : StrongEvolvingNeck K 0 H.epsilon, N.center = y := by
    rintro ⟨N, hN⟩
    apply hfree y ⟨by rw [hX]; exact mem_univ y, hy⟩
    refine ⟨N.terminal_neck, ?_, N.terminal_center.trans hN⟩
    rw [hnecks]
    exact mem_range_self N
  obtain ⟨B₀, hB₀, hyB₀⟩ := (hcover y).resolve_left hynon
  obtain ⟨B, hB, hB₀B, hmaxB⟩ := hmaximal H hε₃ B₀ hB₀
  have hyB : y ∈ B.core := by
    by_contra hn
    exact hynon (hcollar B hB y (hB₀B (B₀.core_subset_carrier hyB₀)) hn)
  have hBA := havoid A B hA hB hmaxA y hyB hyA
  have hpBcore : p ∉ B.core := fun hpB =>
    disjoint_left.mp hBA (B.core_subset_closed_core hpB) (A.core_subset_carrier hpA)
  have hpB : p ∉ B.carrier := fun hpB => hp (hcollar B hB p hpB hpBcore)
  have hAB := havoid B A hB hA hmaxB p hpA hpB
  have hwhole : A.carrier ∪ (T.unionOpen : Set M) ∪ B.carrier = univ :=
    (hclose A B ((H.cap_epsilon A hA).trans_le hε₇)
      ((H.cap_epsilon B hB).trans (H.cap_epsilon A hA).symm)
      H T hT b hshape hBA ⟨y, hy, hyB⟩).1.trans
        (PreconnectedSpace.connectedComponent_eq_univ _)
  refine ⟨A, hA, B, hB, hmaxA, hmaxB, hBA, hAB, T, hT, b, hshape, hwhole, ?_⟩
  intro x hxA hxB hxnon
  have hxAcarrier : x ∉ A.carrier := fun hx => hxnon (hcollar A hA x hx hxA)
  have hxBcarrier : x ∉ B.carrier := fun hx => hxnon (hcollar B hB x hx hxB)
  obtain ⟨D, hD, hxD⟩ := (hcover x).resolve_left hxnon
  have hDA := havoid A D hA hD hmaxA x hxD hxAcarrier
  have hDB := havoid B D hB hD hmaxB x hxD hxBcarrier
  refine ⟨D, hD, hxD, ?_⟩
  intro z hz
  have hzwhole : z ∈ A.carrier ∪ (T.unionOpen : Set M) ∪ B.carrier := by
    rw [hwhole]
    exact mem_univ z
  rcases hzwhole with (hzA | hzT) | hzB
  · exact (disjoint_left.mp hDA hz hzA).elim
  · exact hzT
  · exact (disjoint_left.mp hDB hz hzB).elim

end PoincareConjecture.CompactKappa
