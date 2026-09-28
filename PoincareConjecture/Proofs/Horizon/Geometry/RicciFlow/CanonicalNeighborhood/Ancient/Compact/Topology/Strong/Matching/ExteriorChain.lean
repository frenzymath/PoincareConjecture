import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Extension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Frontier
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.OutgoingChain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.CoreAvoidance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Global

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.CompactKappa

private theorem exists_maximal_outgoing_chain_avoiding
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {g : RiemannianMetric 3 M} (C D : CapCertificate g)
    (H : ConnectedNeckCapCover g) (hsep : C.end_neck.IsSeparating) :
    ∃ T : BalancedNeckChain g C.epsilon,
      C.IsOutgoingChain H T ∧
      (∀ j ∈ T.shape.active, 0 < j → (T.neck j).center ∉ D.carrier) ∧
      ∀ S : BalancedNeckChain g C.epsilon,
        C.IsOutgoingChain H S →
        (∀ j ∈ S.shape.active, 0 < j → (S.neck j).center ∉ D.carrier) →
        T.IsExtension S → S.IsExtension T := by
  classical
  let A := {T : BalancedNeckChain g C.epsilon //
    C.IsOutgoingChain H T ∧
      ∀ j ∈ T.shape.active, 0 < j → (T.neck j).center ∉ D.carrier}
  have : Nonempty A := by
    obtain ⟨T, hT, hshape⟩ := C.exists_singleton_outgoing_chain H hsep
    refine ⟨⟨T, hT, ?_⟩⟩
    intro j hj hpos
    simp only [hshape, ChainShape.active, mem_Icc] at hj
    omega
  let r : A → A → Prop := fun T S => T.1.IsExtension S.1
  have hbound (s : Set A) (hs : IsChain r s) (hne : s.Nonempty) :
      ∃ L : A, ∀ T ∈ s, r T L := by
    let : Nonempty s := hne.to_subtype
    have hdir : Directed BalancedNeckChain.IsExtension (fun T : s => T.1.1) := by
      intro T S
      by_cases he : T.1 = S.1
      · refine ⟨S, ?_, BalancedNeckChain.IsExtension.refl _⟩
        simpa only [he] using BalancedNeckChain.IsExtension.refl S.1.1
      · rcases hs T.2 S.2 he with hTS | hST
        · exact ⟨S, hTS, BalancedNeckChain.IsExtension.refl _⟩
        · exact ⟨T, BalancedNeckChain.IsExtension.refl _, hST⟩
    obtain ⟨L, hactive, hsource, hext, -⟩ :=
      BalancedNeckChain.exists_directed_limit (fun T : s => T.1.1) hdir
    let T₀ : s := Classical.choice inferInstance
    have hstage (j : ℤ) (hj : j ∈ L.shape.active) :
        ∃ T : s, j ∈ T.1.1.shape.active := by
      rw [hactive] at hj
      exact mem_iUnion.mp hj
    have hL : C.IsOutgoingChain H L := by
      constructor
      · exact (hext T₀).1 T₀.1.2.1.zero_active
      · intro j hj
        obtain ⟨T, hjT⟩ := hstage j hj
        exact T.1.2.1.nonnegative j hjT
      · rw [← (hext T₀).2.2 0 T₀.1.2.1.zero_active]
        exact T₀.1.2.1.first_neck
      · intro N hN
        rw [hsource] at hN
        obtain ⟨T, hNT⟩ := mem_iUnion.mp hN
        exact T.1.2.1.source_necks hNT
      · intro j hj hpos
        obtain ⟨T, hjT⟩ := hstage j hj
        rw [← (hext T).2.2 j hjT]
        exact T.1.2.1.centers j hjT hpos
      · intro j hj
        obtain ⟨T, hjT⟩ := hstage j hj
        rw [← (hext T).2.2 j hjT]
        exact T.1.2.1.separating j hjT
      · intro j hj hjnext
        obtain ⟨T, hjT⟩ := hstage j hj
        obtain ⟨S, hjS⟩ := hstage (j + 1) hjnext
        obtain ⟨P, hTP, hSP⟩ := hdir T S
        rw [← (hext P).2.2 j (hTP.1 hjT),
          ← (hext P).2.2 (j + 1) (hSP.1 hjS)]
        exact P.1.2.1.quarter_capture j (hTP.1 hjT) (hSP.1 hjS)
    have havoid : ∀ j ∈ L.shape.active, 0 < j → (L.neck j).center ∉ D.carrier := by
      intro j hj hpos
      obtain ⟨T, hjT⟩ := hstage j hj
      rw [← (hext T).2.2 j hjT]
      exact T.1.2.2 j hjT hpos
    exact ⟨⟨L, hL, havoid⟩, fun T hT => hext ⟨T, hT⟩⟩
  obtain ⟨T, hT⟩ := exists_maximal_of_nonempty_chains_bounded hbound
    (fun hTS hSU => BalancedNeckChain.IsExtension.trans hTS hSU)
  exact ⟨T.1, T.2.1, T.2.2, fun S hS havoid hTS => hT ⟨S, hS, havoid⟩ hTS⟩

private theorem exists_avoiding_outgoing_extension_threshold :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilonStar →
        ∀ (C D : CapCertificate g), C ∈ H.caps →
        ∀ T : BalancedNeckChain g C.epsilon,
          C.IsOutgoingChain H T →
          (∀ j ∈ T.shape.active, 0 < j → (T.neck j).center ∉ D.carrier) →
          ∀ P ∈ H.necks, P.center ∈ H.X \ C.carrier → P.center ∉ D.carrier →
          ∀ b ∈ T.shape.active, b + 1 ∉ T.shape.active →
            P.center ∈ closure ((T.neck b).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) →
            P.center ∉ T.unionOpen →
            ∃ S : BalancedNeckChain g C.epsilon,
              T.IsExtension S ∧ C.IsOutgoingChain H S ∧
              (∀ j ∈ S.shape.active, 0 < j → (S.neck j).center ∉ D.carrier) ∧
              b + 1 ∈ S.shape.active := by
  obtain ⟨epsilon₁, h₁, -, hoverlap⟩ :=
    EpsilonNeck.exists_frontier_reversal_balanced_overlap.{u}
  obtain ⟨epsilon₂, h₂, hsmall, happend⟩ :=
    BalancedNeckChain.exists_append_at_outer_frontier_threshold.{u}
  obtain ⟨epsilon₃, h₃, -, hcapture⟩ :=
    EpsilonNeck.exists_positive_quarter_subset_frontier_neck_inner_slab_threshold.{u}
  refine ⟨min epsilon₁ (min epsilon₂ epsilon₃), lt_min h₁ (lt_min h₂ h₃),
    ((min_le_right _ _).trans (min_le_left _ _)).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H he C D hC T hT havoid P hP hPX hPD
    b hb hnext hfront hout
  have heC := (H.cap_epsilon C hC).trans_le he
  have heb := T.epsilon_eq b hb
  have heP : P.epsilon = C.epsilon :=
    (H.neck_epsilon P hP).trans (H.cap_epsilon C hC).symm
  have houtb : P.center ∉ (T.neck b).carrier :=
    fun hx => hout (mem_iUnion.mpr ⟨⟨b, hb⟩, hx⟩)
  obtain ⟨Q, hsame, hpositive, hnegative, hwithin, -, hQsep⟩ :=
    hoverlap (T.neck b) P (hT.separating b hb)
      (heb.trans_le (heC.trans (min_le_left _ _))) (heP.trans heb.symm)
      (by simpa only [heb] using hfront) houtb
  have heQ : Q.epsilon = C.epsilon := hsame.epsilon_eq.trans heP
  have hQfront : Q.center ∈ closure
      ((T.neck b).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) := by rwa [hsame.center_eq]
  obtain ⟨S, hshape, hext, hsource, hnew, -⟩ :=
    happend T Q P (heC.trans ((min_le_right _ _).trans (min_le_left _ _))) heQ hsame
      hT.separating b hb hnext hQfront (by rwa [hsame.center_eq])
      (by simpa only [heb] using hpositive) (by simpa only [heb] using hnegative)
      (by simpa only [heb] using hwithin)
  have hactive : S.shape.active = insert (b + 1) T.shape.active := by
    rw [hshape, ChainShape.extendRight_active hb hnext]
  have hS : C.IsOutgoingChain H S := by
    constructor
    · exact hext.1 hT.zero_active
    · intro j hj
      rw [hactive, mem_insert_iff] at hj
      rcases hj with rfl | hj
      · have := hT.nonnegative b hb
        omega
      · exact hT.nonnegative j hj
    · rw [← hext.2.2 0 hT.zero_active]
      exact hT.first_neck
    · rw [hsource]
      exact insert_subset (mem_insert_of_mem _ hP) hT.source_necks
    · intro j hj hpos
      rw [hactive, mem_insert_iff] at hj
      rcases hj with rfl | hj
      · rwa [hnew, hsame.center_eq]
      · rw [← hext.2.2 j hj]
        exact hT.centers j hj hpos
    · intro j hj
      rw [hactive, mem_insert_iff] at hj
      rcases hj with rfl | hj
      · rwa [hnew]
      · rw [← hext.2.2 j hj]
        exact hT.separating j hj
    · apply hT.quarter_capture.of_append hext hb hnext hshape
      rw [hnew]
      have hslab := hcapture (T.neck b) Q
        (heb.trans_le (heC.trans ((min_le_right _ _).trans (min_le_right _ _))))
        (heQ.trans heb.symm) (by simpa only [heb] using hQfront)
      intro x hx
      exact hslab (by simpa only [heb] using hx)
  refine ⟨S, hext, hS, ?_, hactive.symm ▸ mem_insert (b + 1) T.shape.active⟩
  intro j hj hpos
  rw [hactive, mem_insert_iff] at hj
  rcases hj with rfl | hj
  · rwa [hnew, hsame.center_eq]
  · rw [← hext.2.2 j hj]
    exact havoid j hj hpos

theorem exists_two_core_avoiding_outgoing_chain_threshold :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [ConnectedSpace M] {g : RiemannianMetric 3 M},
        ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilonStar → H.X = univ →
        ∀ (C D : CapCertificate g), C ∈ H.caps → D ∈ H.caps → H.caps ⊆ {C, D} →
          Disjoint D.closed_core C.carrier → IsCompact (univ : Set M) →
          ∃ (T : BalancedNeckChain g C.epsilon) (b : ℤ),
            C.IsOutgoingChain H T ∧ T.shape = .finite 0 b ∧
            (∀ j ∈ T.shape.active, 0 < j → (T.neck j).center ∉ D.carrier) ∧
            frontier (C.carrier ∪ (T.unionOpen : Set M)) ⊆ D.carrier ∧
            Disjoint C.closed_core (T.unionOpen : Set M) ∧
            Disjoint D.closed_core (T.unionOpen : Set M) := by
  obtain ⟨epsilon₁, h₁, hsmall, hsep⟩ :=
    CapCertificate.exists_end_neck_separating_threshold.{u}
  obtain ⟨epsilon₂, h₂, -, hextend⟩ := exists_avoiding_outgoing_extension_threshold.{u}
  obtain ⟨epsilon₃, h₃, -, hfrontier⟩ :=
    CapCertificate.exists_chain_frontier_positive_end_threshold.{u}
  obtain ⟨epsilon₄, h₄, -, hcapped⟩ :=
    CapCertificate.exists_outgoing_capped_tube_threshold.{u}
  obtain ⟨epsilon₅, h₅, hsmall₅, havoid⟩ :=
    CapCertificate.exists_exterior_center_neck_disjoint_closed_core_threshold.{u}
  obtain ⟨epsilon₆, h₆, -, hinter⟩ :=
    CapCertificate.exists_chain_intersection_threshold.{u}
  let epsilonStar := min epsilon₁
    (min epsilon₂ (min epsilon₃ (min epsilon₄ (min epsilon₅ epsilon₆))))
  refine ⟨epsilonStar, lt_min h₁ (lt_min h₂ (lt_min h₃ (lt_min h₄ (lt_min h₅ h₆)))),
    ?_, ?_⟩
  · exact ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))).trans hsmall₅
  intro M _ _ _ _ _ _ _ _ g H he hX C D hC hD hcaps hDC hcompact
  have hepsilon : H.epsilon ≤ epsilon₁ ∧ H.epsilon ≤ epsilon₂ ∧
      H.epsilon ≤ epsilon₃ ∧ H.epsilon ≤ epsilon₄ ∧
      H.epsilon ≤ epsilon₅ ∧ H.epsilon ≤ epsilon₆ := by
    simpa only [epsilonStar, le_min_iff] using he
  obtain ⟨he₁, he₂, he₃, he₄, he₅, he₆⟩ := hepsilon
  have heC := H.cap_epsilon C hC
  have heD := H.cap_epsilon D hD
  obtain ⟨T, hT, hTD, hmax⟩ := exists_maximal_outgoing_chain_avoiding C D H
    (hsep C (heC.trans_le he₁))
  have hfrontD : frontier (C.carrier ∪ (T.unionOpen : Set M)) ⊆ D.carrier := by
    intro x hx
    by_contra hxD
    have hout := ((C.carrier_open.union T.unionOpen.isOpen).frontier_eq ▸ hx).2
    have hxX : x ∈ H.X := hX.symm ▸ mem_univ x
    rcases H.pointwise_cover x hxX with ⟨P, hP, hp⟩ | ⟨E, hE, hxE⟩
    · obtain ⟨b, hb, hnext, hpos⟩ := hfrontier C (heC.trans_le he₃) T
        hT.zero_active hT.nonnegative hT.first_neck hT.quarter_capture x hx
      obtain ⟨S, hext, hS, hSD, hnew⟩ := hextend H he₂ C D hC T hT hTD P hP
        (hp.symm ▸ ⟨hxX, fun h => hout (Or.inl h)⟩) (hp.symm ▸ hxD)
        b hb hnext (hp.symm ▸ hpos) (hp.symm ▸ (fun h => hout (Or.inr h)))
      exact hnext ((hmax S hS hSD hext).1 hnew)
    · rcases mem_insert_iff.mp (hcaps hE) with hEC | hED
      · exact hout (Or.inl (C.core_subset_carrier (hEC ▸ hxE)))
      · exact hxD (D.core_subset_carrier (mem_singleton_iff.mp hED ▸ hxE))
  have hfrontNonempty : (frontier (C.carrier ∪ (T.unionOpen : Set M))).Nonempty := by
    by_contra hn
    have hfrontEmpty := not_nonempty_iff_eq_empty.mp hn
    rcases frontier_eq_empty_iff.mp hfrontEmpty with hempty | hwhole
    · obtain ⟨x, hx⟩ := C.core_nonempty
      have hxU : x ∈ C.carrier ∪ (T.unionOpen : Set M) :=
        Or.inl (C.core_subset_carrier hx)
      exact (hempty ▸ hxU : x ∈ (∅ : Set M))
    · obtain ⟨A, -, -, -, hA⟩ := hcapped C (heC.trans_le he₄) H T hT
      exact A.not_isCompact_carrier ((hA.trans hwhole).symm ▸ hcompact)
  obtain ⟨x, hx⟩ := hfrontNonempty
  obtain ⟨b, hb, hnext, -⟩ := hfrontier C (heC.trans_le he₃) T
    hT.zero_active hT.nonnegative hT.first_neck hT.quarter_capture x hx
  refine ⟨T, b, hT, hT.shape_eq_finite_of_right_endpoint hb hnext,
    hTD, hfrontD, ?_, ?_⟩
  · exact (hinter C (heC.trans_le he₆) T 0 hT.zero_active hT.first_neck
      hT.nonnegative (fun j hj hp => (hT.centers j hj hp).2)).2.1
  · apply disjoint_left.mpr
    intro y hyD hyT
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hyT
    rcases (hT.nonnegative j.1 j.2).eq_or_lt with hj | hj
    · have heq : T.neck j.1 = C.end_neck := hj ▸ hT.first_neck
      exact disjoint_left.mp hDC hyD (C.end_neck_subset (heq ▸ hyj))
    · exact disjoint_left.mp (havoid D (T.neck j.1) (heD.trans_le he₅)
        ((T.epsilon_eq j.1 j.2).trans (heC.trans heD.symm))
        (hTD j.1 j.2 hj)) hyD hyj

end PoincareConjecture.CompactKappa
