import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Selection.Maximal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.LocalRegions.CapChain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.OutgoingChain













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.CompactKappa



theorem exists_outgoing_chain_with_neck_free_frontier_threshold :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ epsilonStar →
        ∀ A ∈ H.caps, ∃ T : BalancedNeckChain g A.epsilon,
          A.IsOutgoingChain H T ∧
          ∀ x ∈ H.X ∩ frontier (A.carrier ∪ (T.unionOpen : Set M)),
            ¬ ∃ N ∈ H.necks, N.center = x := by
  obtain ⟨epsilon₁, h₁, hsmall, hmaximal⟩ :=
    CapCertificate.exists_maximal_outgoing_chain_threshold.{u}
  obtain ⟨epsilon₂, h₂, _, hfrontier⟩ :=
    CapCertificate.exists_chain_frontier_positive_end_threshold.{u}
  obtain ⟨epsilon₃, h₃, _, hextend⟩ :=
    CapCertificate.exists_outgoing_chain_extension_threshold.{u}
  refine ⟨min epsilon₁ (min epsilon₂ epsilon₃), lt_min h₁ (lt_min h₂ h₃),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H hε A hA
  obtain ⟨T, hT, hmax⟩ := hmaximal H (hε.trans (min_le_left _ _)) A hA
  refine ⟨T, hT, ?_⟩
  rintro x hx ⟨N, hN, hcenter⟩
  obtain ⟨b, hb, hnext, hpositive⟩ := hfrontier A
    ((H.cap_epsilon A hA).trans_le
      (hε.trans ((min_le_right _ _).trans (min_le_left _ _))))
    T hT.zero_active hT.nonnegative hT.first_neck hT.quarter_capture x hx.2
  have hout : x ∉ A.carrier ∪ (T.unionOpen : Set M) :=
    ((A.carrier_open.union T.unionOpen.isOpen).frontier_eq ▸ hx.2).2
  have hNX : N.center ∈ H.X \ A.carrier := by
    rw [hcenter]
    exact ⟨hx.1, fun h => hout (Or.inl h)⟩
  obtain ⟨S, hext, hS, hnew⟩ := hextend H
    (hε.trans ((min_le_right _ _).trans (min_le_right _ _))) A hA T hT N hN hNX
    b hb hnext (hcenter.symm ▸ hpositive)
    (by rw [hcenter]; exact fun h => hout (Or.inr h))
  exact hnext ((hmax S hS hext).1 hnew)




theorem exists_finite_outgoing_chain_non_strong_endpoint_threshold :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {epsilon C : ℝ}
        (hepsilon : 0 < epsilon),
        epsilon ≤ epsilonStar → ∀ hC : 0 < C,
        IsCompact (univ : Set M) →
        ∀ hcover : ∀ p : M,
          (∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p) ∨
          (∃ A : CapCertificate (K.flow.metric 0),
            A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ p ∈ A.core),
        ∀ (A : CapCertificate (K.flow.metric 0)) (hA : A.epsilon = epsilon),
          A.cap_constant ≤ C →
          ∃ T : BalancedNeckChain (K.flow.metric 0) A.epsilon,
            A.IsOutgoingChain
              (strongNeckCapWholeCover K hepsilon (hA ▸ A.epsilon_le_threshold) hC hcover) T ∧
            ∃ b : ℤ, T.shape = .finite 0 b ∧
              ∃ x ∈ frontier (A.carrier ∪ (T.unionOpen : Set M)),
                x ∉ A.carrier ∧
                ¬ ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  obtain ⟨epsilon₁, h₁, hsmall, hchain⟩ :=
    exists_outgoing_chain_with_neck_free_frontier_threshold.{u}
  obtain ⟨epsilon₂, h₂, _, hcapped⟩ :=
    CapCertificate.exists_outgoing_capped_tube_threshold.{u}
  obtain ⟨epsilon₃, h₃, _, hfrontier⟩ :=
    CapCertificate.exists_chain_frontier_positive_end_threshold.{u}
  refine ⟨min epsilon₁ (min epsilon₂ epsilon₃), lt_min h₁ (lt_min h₂ h₃),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K epsilon C hepsilon hε hC hcompact hcover A hA hAC
  let H := strongNeckCapWholeCover K hepsilon (hA ▸ A.epsilon_le_threshold) hC hcover
  obtain ⟨T, hT, hfree⟩ := hchain H (hε.trans (min_le_left _ _)) A ⟨hA, hAC⟩
  obtain ⟨tube, _, _, _, hcarrier⟩ := hcapped A
    (hA.trans_le (hε.trans ((min_le_right _ _).trans (min_le_left _ _)))) H T hT
  have hproper : A.carrier ∪ (T.unionOpen : Set M) ≠ univ := by
    intro hwhole
    exact tube.not_isCompact_carrier ((hcarrier.trans hwhole).symm ▸ hcompact)
  have hnonempty : (A.carrier ∪ (T.unionOpen : Set M)).Nonempty := by
    obtain ⟨a, ha⟩ := A.core_nonempty
    exact ⟨a, Or.inl (A.core_subset_carrier ha)⟩
  have hfrontnonempty : (frontier (A.carrier ∪ (T.unionOpen : Set M))).Nonempty := by
    by_contra hn
    have hfront := not_nonempty_iff_eq_empty.mp hn
    rcases frontier_eq_empty_iff.mp hfront with hempty | hwhole
    · exact hnonempty.ne_empty hempty
    · exact hproper hwhole
  obtain ⟨x, hx⟩ := hfrontnonempty
  obtain ⟨b, hb, hnext, _⟩ := hfrontier A
    (hA.trans_le (hε.trans ((min_le_right _ _).trans (min_le_right _ _))))
    T hT.zero_active hT.nonnegative hT.first_neck hT.quarter_capture x hx
  refine ⟨T, hT, b, hT.shape_eq_finite_of_right_endpoint hb hnext, x, hx, ?_, ?_⟩
  · intro hxA
    exact ((A.carrier_open.union T.unionOpen.isOpen).frontier_eq ▸ hx).2 (Or.inl hxA)
  · rintro ⟨N, hN⟩
    exact hfree x ⟨mem_univ x, hx⟩
      ⟨N.terminal_neck, mem_range_self N, N.terminal_center.trans hN⟩

end PoincareConjecture.CompactKappa
