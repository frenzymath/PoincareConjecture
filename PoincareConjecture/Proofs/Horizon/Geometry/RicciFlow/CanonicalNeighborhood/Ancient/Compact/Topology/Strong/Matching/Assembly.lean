import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.DoubleCapped
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Strong.Matching.ExteriorChain
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Strong.Matching.Overlap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Strong.Matching.Whole
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.Orientation













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.CompactKappa



theorem exists_strongDoubleCappedTube_with_cores_of_two_caps_threshold :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {epsilon C : ℝ}
        (cap₁ cap₂ : CapCertificate (K.flow.metric 0)),
        IsCompact (univ : Set M) →
        cap₁.epsilon = epsilon → cap₂.epsilon = epsilon →
        cap₁.cap_constant ≤ C → cap₂.cap_constant ≤ C → epsilon ≤ epsilonStar →
        Disjoint cap₁.closed_core cap₂.carrier →
        Disjoint cap₂.closed_core cap₁.carrier →
        (∀ x : M, x ∉ cap₁.core → x ∉ cap₂.core →
          ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) →
        ∃ S : M26StrongDoubleCappedTube K 0 epsilon C,
          S.cap₁.cap.core = cap₁.core ∧ S.cap₂.cap.core = cap₂.core ∧
          (∀ x : M, x ∉ S.cap₁.cap.core → x ∉ S.cap₂.cap.core →
            ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) := by
  obtain ⟨epsilon₁, h₁, hsmall, hchain⟩ :=
    exists_two_core_avoiding_outgoing_chain_threshold.{u}
  obtain ⟨epsilon₂, h₂, -, hwhole⟩ := exists_whole_cover_of_frontier_in_cap_threshold.{u}
  obtain ⟨epsilon₃, h₃, -, htube⟩ :=
    BalancedNeckChain.exists_finite_tubeCertificate_threshold.{u}
  obtain ⟨epsilon₄, h₄, -, hoverlap⟩ :=
    exists_second_cap_overlap_of_carrier_contact_threshold.{u}
  obtain ⟨epsilon₅, h₅, -, htails⟩ :=
    CapCertificate.exists_opposite_cylinder_tails_of_compact_closing_threshold.{u}
  obtain ⟨epsilon₆, h₆, -, hcapTail⟩ :=
    CapCertificate.exists_second_cap_tail_of_compact_closing_threshold.{u}
  let epsilonStar := min epsilon₁
    (min epsilon₂ (min epsilon₃ (min epsilon₄ (min epsilon₅ epsilon₆))))
  have hstar : 0 < epsilonStar :=
    lt_min h₁ (lt_min h₂ (lt_min h₃ (lt_min h₄ (lt_min h₅ h₆))))
  have hstarSmall : epsilonStar ≤ 1 / 200 :=
    (min_le_left _ _).trans (hsmall.trans (by norm_num))
  refine ⟨epsilonStar, hstar, hstarSmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K epsilon C cap₁ cap₂ hcompact he₁ he₂ hC₁ hC₂
    he hCD hDC hstrong
  classical
  have hepsilon : epsilon ≤ epsilon₁ ∧ epsilon ≤ epsilon₂ ∧
      epsilon ≤ epsilon₃ ∧ epsilon ≤ epsilon₄ ∧ epsilon ≤ epsilon₅ ∧
      epsilon ≤ epsilon₆ := by
    simpa only [epsilonStar, le_min_iff] using he
  obtain ⟨hε₁, hε₂, hε₃, hε₄, hε₅, hε₆⟩ := hepsilon
  let H : ConnectedNeckCapCover (K.flow.metric 0) := {
    epsilon := epsilon
    epsilon_pos := he₁ ▸ cap₁.epsilon_pos
    epsilon_threshold := epsilonStar
    epsilon_threshold_pos := hstar
    epsilon_threshold_le_one_two_hundred := hstarSmall
    epsilon_le_threshold := he
    cap_constant := C
    cap_constant_pos := cap₁.cap_constant_pos.trans_le hC₁
    X := univ
    connected_X := isConnected_univ
    necks := range (fun N : StrongEvolvingNeck K 0 epsilon => N.terminal_neck)
    caps := {cap₁, cap₂}
    pointwise_cover := by
      intro x _
      by_cases hx₁ : x ∈ cap₁.core
      · exact Or.inr ⟨cap₁, mem_insert _ _, hx₁⟩
      by_cases hx₂ : x ∈ cap₂.core
      · exact Or.inr ⟨cap₂, mem_insert_of_mem _ (mem_singleton _), hx₂⟩
      obtain ⟨N, hN⟩ := hstrong x hx₁ hx₂
      exact Or.inl ⟨N.terminal_neck, mem_range_self N, N.terminal_center.trans hN⟩
    neck_epsilon := by
      rintro N ⟨E, rfl⟩
      exact E.terminal_epsilon
    cap_epsilon := by
      intro D hD
      rcases mem_insert_iff.mp hD with rfl | hD
      · exact he₁
      · exact mem_singleton_iff.mp hD ▸ he₂
    cap_constant_bound := by
      intro D hD
      rcases mem_insert_iff.mp hD with rfl | hD
      · exact hC₁
      · exact mem_singleton_iff.mp hD ▸ hC₂ }
  obtain ⟨T, b, hT, hshape, -, hfront, havoid₁, havoid₂⟩ :=
    hchain H hε₁ rfl cap₁ cap₂ (mem_insert _ _)
      (mem_insert_of_mem _ (mem_singleton _)) Subset.rfl hDC hcompact
  letI : CompactSpace M := isCompact_univ_iff.mp hcompact
  have hmeet : ((cap₁.carrier ∪ (T.unionOpen : Set M)) \ cap₂.carrier).Nonempty := by
    obtain ⟨x, hx⟩ := cap₁.core_nonempty
    exact ⟨x, Or.inl (cap₁.core_subset_carrier hx),
      fun h => disjoint_left.mp hCD (cap₁.core_subset_closed_core hx) h⟩
  have hfull := hwhole cap₂ (he₂.trans_le hε₂)
    (cap₁.carrier ∪ (T.unionOpen : Set M)) (cap₁.carrier_open.union T.unionOpen.isOpen)
    isClosed_frontier.isCompact hfront hmeet
  obtain ⟨tube, hetube, -, hcarrier⟩ := htube T (he₁.trans_le hε₃) 0 b hshape ∅
    (empty_subset _)
  rw [← hcarrier] at hfull hfront havoid₁ havoid₂
  have hend : cap₁.end_neck.carrier ⊆ tube.carrier := by
    rw [hcarrier]
    intro x hx
    exact mem_iUnion.mpr ⟨⟨0, hT.zero_active⟩, hT.first_neck.symm ▸ hx⟩
  have hfirstOverlap : cap₁.carrier ∩ tube.carrier = cap₁.end_neck.carrier := by
    apply Subset.antisymm
    · rintro x ⟨hxC, hxT⟩
      rcases cap₁.carrier_eq_closed_core_union_end ▸ hxC with hxcore | hxend
      · exact (disjoint_left.mp havoid₁ hxcore hxT).elim
      · exact hxend
    · exact fun _ hx => ⟨cap₁.end_neck_subset hx, hend hx⟩
  have firstModel : OpenCylinderModel (cap₁.carrier ∩ tube.carrier) :=
    hfirstOverlap.symm ▸ cap₁.end_neck.openCylinderModel
  have hnonempty : (frontier (cap₁.carrier ∪ tube.carrier)).Nonempty := by
    by_contra hn
    rcases frontier_eq_empty_iff.mp (not_nonempty_iff_eq_empty.mp hn) with hempty | hwhole'
    · obtain ⟨x, hx⟩ := cap₁.core_nonempty
      have hxU : x ∈ cap₁.carrier ∪ tube.carrier := Or.inl (cap₁.core_subset_carrier hx)
      exact (hempty ▸ hxU : x ∈ (∅ : Set M))
    · obtain ⟨x, hx⟩ := cap₂.core_nonempty
      have hxU : x ∈ cap₁.carrier ∪ tube.carrier := hwhole'.symm ▸ mem_univ x
      exact hxU.elim
        (fun h => disjoint_left.mp hDC (cap₂.core_subset_closed_core hx) h)
        (fun h => disjoint_left.mp havoid₂ (cap₂.core_subset_closed_core hx) h)
  have hunionCompact : IsCompact (cap₁.carrier ∪ tube.carrier ∪ cap₂.carrier) :=
    hfull.symm ▸ hcompact
  have hcontact : (frontier (cap₁.carrier ∪ tube.carrier) ∩ cap₂.carrier).Nonempty := by
    obtain ⟨x, hx⟩ := hnonempty
    exact ⟨x, hx, hfront hx⟩
  obtain ⟨secondModel⟩ := hoverlap cap₁ cap₂ (he₂.trans_le hε₄)
    ⟨tube.carrier, tube.carrier_open⟩ tube.cylinder hend havoid₁ hCD hunionCompact hcontact
  obtain ⟨side, hfirstTail, hsecondTail⟩ := htails cap₁ cap₂ (he₁.trans_le hε₅)
    tube.carrier tube.cylinder hend havoid₁ tube.carrier_open hnonempty hunionCompact
  have hsecondCapTail := hcapTail cap₁ cap₂ (he₂.trans_le hε₆)
    tube.carrier_open hend hCD hunionCompact
  have hfirstCapTail : ∃ s ∈ Ioo 0 cap₁.epsilon⁻¹,
      cap₁.end_neck.region s cap₁.epsilon⁻¹ ⊆ tube.carrier := by
    have hr := inv_pos.mpr cap₁.epsilon_pos
    exact ⟨cap₁.epsilon⁻¹ / 2, by constructor <;> linarith,
      (cap₁.end_neck.region_subset_carrier _ _).trans hend⟩
  let first : CapTubeAttachment cap₁ tube side :=
    ⟨firstModel, hfirstTail, hfirstCapTail⟩
  let second : CapTubeAttachment cap₂ tube (!side) :=
    ⟨secondModel, hsecondTail, hsecondCapTail⟩
  have hstrongTube : ∀ x ∈ tube.carrier,
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
    intro x hx
    exact hstrong x
      (fun h => disjoint_left.mp havoid₁ (cap₁.core_subset_closed_core h) hx)
      (fun h => disjoint_left.mp havoid₂ (cap₂.core_subset_closed_core h) hx)
  have hmake (tube' : EpsilonTubeCertificate (K.flow.metric 0) ∅)
      (hcarrier' : tube'.carrier = tube.carrier) (he' : tube'.epsilon = epsilon)
      (first' : CapTubeAttachment cap₁ tube' false)
      (second' : CapTubeAttachment cap₂ tube' true) :
      ∃ S : M26StrongDoubleCappedTube K 0 epsilon C,
        S.cap₁.cap.core = cap₁.core ∧ S.cap₂.cap.core = cap₂.core ∧
        (∀ x : M, x ∉ S.cap₁.cap.core → x ∉ S.cap₂.cap.core →
          ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) := by
    have hfull' : cap₁.carrier ∪ tube'.carrier ∪ cap₂.carrier = univ := by
      rw [hcarrier']
      exact hfull
    let A : DoubleCappedTubeCertificate (K.flow.metric 0) := {
      carrier := univ
      cap₁ := cap₁
      cap₂ := cap₂
      tube := tube'
      cap₁_subset := subset_univ _
      cap₂_subset := subset_univ _
      tube_subset := subset_univ _
      carrier_eq_union := hfull'.symm
      disjoint_cores := hCD.mono_right cap₂.closed_core_subset_carrier
      connected := isConnected_univ
      compact := hcompact
      first_attachment := first'
      second_attachment := second' }
    exact ⟨compactStrongDoubleCappedTube K le_rfl A he₁ he₂ he' hC₁ hC₂
      (fun x hx => hstrongTube x (hcarrier' ▸ hx)) rfl, rfl, rfl, hstrong⟩
  cases side
  · exact hmake tube rfl (hetube.trans he₁) first second
  · exact hmake tube.reversedCylinder rfl (hetube.trans he₁)
      first.reversedCylinder second.reversedCylinder

end PoincareConjecture.CompactKappa
