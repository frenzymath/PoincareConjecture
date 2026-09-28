import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Cap
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.LocalRegions.CapChain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.OutgoingChain

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

theorem exists_coveredCappedTube_of_cap_threshold :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {epsilon C : ℝ}
        (cap : CapCertificate (K.flow.metric 0)),
        cap.epsilon = epsilon → cap.cap_constant ≤ C → epsilon ≤ epsilonStar →
        (∀ x : M, x ∉ cap.core →
          ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) →
        ∃ A : CappedTubeCertificate (K.flow.metric 0),
          A.cap = cap ∧ A.tube.epsilon = epsilon ∧ A.carrier = univ ∧
            Disjoint cap.closed_core A.tube.carrier := by
  obtain ⟨epsilon₁, h₁, hsmall, hchain⟩ :=
    ConnectedNeckCapCover.exists_outgoing_chain_cover_or_cap_threshold.{u}
  obtain ⟨epsilon₂, h₂, -, hcapped⟩ :=
    CapCertificate.exists_outgoing_capped_tube_threshold.{u}
  obtain ⟨epsilon₃, h₃, -, hinter⟩ :=
    CapCertificate.exists_chain_intersection_threshold.{u}
  let epsilonStar := min epsilon₁ (min epsilon₂ epsilon₃)
  have hstar : 0 < epsilonStar := lt_min h₁ (lt_min h₂ h₃)
  have hstar₁ : epsilonStar ≤ epsilon₁ := min_le_left _ _
  have hstar₂ : epsilonStar ≤ epsilon₂ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hstar₃ : epsilonStar ≤ epsilon₃ :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hstarSmall : epsilonStar ≤ 1 / 200 :=
    (hstar₁.trans hsmall).trans (by norm_num)
  refine ⟨epsilonStar, hstar, hstarSmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K epsilon C cap hcap hconstant hepsilon hstrong
  classical
  let H : ConnectedNeckCapCover (K.flow.metric 0) := {
    epsilon := epsilon
    epsilon_pos := hcap ▸ cap.epsilon_pos
    epsilon_threshold := epsilonStar
    epsilon_threshold_pos := hstar
    epsilon_threshold_le_one_two_hundred := hstarSmall
    epsilon_le_threshold := hepsilon
    cap_constant := cap.cap_constant
    cap_constant_pos := cap.cap_constant_pos
    X := univ
    connected_X := isConnected_univ
    necks := range (fun N : StrongEvolvingNeck K 0 epsilon => N.terminal_neck)
    caps := {cap}
    pointwise_cover := by
      intro x _
      by_cases hx : x ∈ cap.core
      · exact Or.inr ⟨cap, mem_singleton _, hx⟩
      · obtain ⟨N, hN⟩ := hstrong x hx
        exact Or.inl ⟨N.terminal_neck, mem_range_self N, N.terminal_center.trans hN⟩
    neck_epsilon := by
      rintro N ⟨E, rfl⟩
      exact E.terminal_epsilon
    cap_epsilon := by
      rintro D (rfl : D = cap)
      exact hcap
    cap_constant_bound := by
      rintro D (rfl : D = cap)
      exact le_rfl }
  have hcapmem : cap ∈ H.caps := mem_singleton _
  have hmeet : (H.X ∩ cap.carrier).Nonempty := by
    obtain ⟨x, hx⟩ := cap.core_nonempty
    exact ⟨x, mem_univ _, cap.core_subset_carrier hx⟩
  obtain ⟨T, hT, hcover⟩ := hchain H (hepsilon.trans hstar₁) cap hcapmem hmeet
  have hwhole : cap.carrier ∪ (T.unionOpen : Set M) = univ := by
    apply Subset.antisymm (subset_univ _)
    rcases hcover with hcover | ⟨x, hx, D, hD, hxD⟩
    · exact hcover
    · have hDcap : D = cap := mem_singleton_iff.mp hD
      subst D
      have hout := ((cap.carrier_open.union T.unionOpen.isOpen).frontier_eq ▸ hx.2).2
      exact False.elim (hout (Or.inl (cap.core_subset_carrier hxD)))
  obtain ⟨A, hAcap, hAepsilon, hAchain, hAcarrier⟩ :=
    hcapped cap (hcap.trans_le (hepsilon.trans hstar₂)) H T hT
  obtain ⟨-, hdisjoint, -⟩ := hinter cap
    (hcap.trans_le (hepsilon.trans hstar₃)) T 0 hT.zero_active hT.first_neck
    hT.nonnegative (fun j hj hpos => (hT.centers j hj hpos).2)
  have hchains :
      (Sigma.mk A.tube.epsilon A.tube.chain :
        (e : ℝ) × BalancedNeckChain (K.flow.metric 0) e) =
      Sigma.mk cap.epsilon T := Sigma.ext hAepsilon hAchain
  have htube : A.tube.carrier = (T.unionOpen : Set M) := by
    calc
      A.tube.carrier = (A.tube.chain.unionOpen : Set M) := A.tube.carrier_eq_chain_union
      _ = (T.unionOpen : Set M) := congrArg
        (fun S : (e : ℝ) × BalancedNeckChain (K.flow.metric 0) e =>
          (S.2.unionOpen : Set M)) hchains
  exact ⟨A, hAcap, hAepsilon.trans hcap, hAcarrier.trans hwhole, htube ▸ hdisjoint⟩

theorem exists_strongCappedTube_preserving_cap_threshold :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {epsilon C : ℝ}
        (cap : CapCertificate (K.flow.metric 0)),
        cap.epsilon = epsilon → cap.cap_constant ≤ C → epsilon ≤ epsilonStar →
        (∀ x : M, x ∉ cap.core →
          ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) →
        ∃ T : M26StrongCappedTube K 0 epsilon C,
          T.cap.cap.core = cap.core ∧ T.cap.cap.closed_core = cap.closed_core ∧
            ∀ x : M, x ∈ T.cap.cap.core ∨
              ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  obtain ⟨epsilonStar, hstar, hsmall, hmake⟩ :=
    exists_coveredCappedTube_of_cap_threshold.{u}
  refine ⟨epsilonStar, hstar, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K epsilon C cap hcap hconstant hepsilon hstrong
  classical
  obtain ⟨A, hAcap, hAepsilon, hwhole, hdisjoint⟩ :=
    hmake K cap hcap hconstant hepsilon hstrong
  let T := strongCappedTubeOfCappedTube K le_rfl A
    (hAcap ▸ hcap) hAepsilon (hAcap ▸ hconstant)
    (fun x hx => hstrong x (fun hcore =>
      disjoint_left.mp hdisjoint (cap.core_subset_closed_core hcore) hx)) hwhole
  have hcore : T.cap.cap.core = cap.core := by
    change A.cap.core = cap.core
    exact congrArg CapCertificate.core hAcap
  have hclosed : T.cap.cap.closed_core = cap.closed_core := by
    change A.cap.closed_core = cap.closed_core
    exact congrArg CapCertificate.closed_core hAcap
  refine ⟨T, hcore, hclosed, ?_⟩
  intro x
  by_cases hx : x ∈ cap.core
  · exact Or.inl (hcore ▸ hx)
  · exact Or.inr (hstrong x hx)

theorem exists_strongCappedTube_of_cap_threshold :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {epsilon C : ℝ}
        (cap : CapCertificate (K.flow.metric 0)),
        cap.epsilon = epsilon → cap.cap_constant ≤ C → epsilon ≤ epsilonStar →
        (∀ x : M, x ∉ cap.core →
          ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) →
        Nonempty (M26StrongCappedTube K 0 epsilon C) := by
  obtain ⟨epsilonStar, hstar, hsmall, hmake⟩ :=
    exists_strongCappedTube_preserving_cap_threshold.{u}
  refine ⟨epsilonStar, hstar, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K epsilon C cap hcap hconstant hepsilon hstrong
  obtain ⟨T, _, _, _⟩ := hmake K cap hcap hconstant hepsilon hstrong
  exact ⟨T⟩

end PoincareConjecture.NoncompactKappa.Positive
