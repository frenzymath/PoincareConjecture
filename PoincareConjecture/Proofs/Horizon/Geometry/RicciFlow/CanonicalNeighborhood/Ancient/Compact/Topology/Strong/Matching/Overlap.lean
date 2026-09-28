import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.CapOverlap

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CompactKappa

theorem exists_second_cap_overlap_of_carrier_contact_threshold :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), D.epsilon ≤ epsilonStar →
          ∀ (U : Opens M) (T : OpenCylinderModel (U : Set M)),
            C.end_neck.carrier ⊆ U → Disjoint C.closed_core (U : Set M) →
            Disjoint C.closed_core D.carrier →
            IsCompact (C.carrier ∪ (U : Set M) ∪ D.carrier) →
            (frontier (C.carrier ∪ (U : Set M)) ∩ D.carrier).Nonempty →
            Nonempty (OpenCylinderModel (D.carrier ∩ (U : Set M))) := by
  obtain ⟨epsilon₁, h₁, hsmall, htail⟩ :=
    CapCertificate.exists_second_cap_tail_of_compact_closing_threshold.{u}
  obtain ⟨epsilon₂, h₂, -, htrunc⟩ :=
    CapCertificate.exists_truncated_core_domain_threshold.{u}
  refine ⟨min epsilon₁ epsilon₂, lt_min h₁ h₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D he U T hend hfirst hCD hcompact hcontact
  obtain ⟨x, hxfront, hxD⟩ := hcontact
  obtain ⟨a, ha, htaila⟩ := htail C D (he.trans (min_le_left _ _))
    U.isOpen hend hCD hcompact
  have hR : 0 < D.epsilon⁻¹ := inv_pos.mpr D.epsilon_pos
  obtain ⟨t, hat, htR, hxt⟩ : ∃ t : ℝ, a < t ∧ t < D.epsilon⁻¹ ∧
      x ∈ D.closed_core ∪ D.end_neck.region (-D.epsilon⁻¹) t := by
    rcases D.carrier_eq_closed_core_union_end ▸ hxD with hxcore | hxend
    · obtain ⟨t, hat, htR⟩ := exists_between ha.2
      exact ⟨t, hat, htR, Or.inl hxcore⟩
    · have hxcoord := (D.end_neck.coordinate_inverse_mem x hxend).2
      rw [D.end_neck_epsilon] at hxcoord
      obtain ⟨t, ht, htR⟩ := exists_between (max_lt ha.2 hxcoord.2)
      exact ⟨t, (le_max_left _ _).trans_lt ht, htR,
        Or.inr ⟨hxend, hxcoord.1, (le_max_right _ _).trans_lt ht⟩⟩
  let s := (t + D.epsilon⁻¹) / 2
  let delta := (D.epsilon⁻¹ - t) / 4
  have hs : s ∈ Ioo 0 D.epsilon⁻¹ := by
    dsimp [s]
    constructor <;> linarith [ha.1]
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have htl : t < s - delta := by dsimp [s, delta]; linarith
  have hlo : 0 < s - delta := ha.1.trans (hat.trans htl)
  have hhi : s + delta < D.epsilon⁻¹ := by dsimp [s, delta]; linarith
  have hs' : s ∈ Ioo (-D.end_neck.epsilon⁻¹) D.end_neck.epsilon⁻¹ := by
    rw [D.end_neck_epsilon]
    exact ⟨(neg_lt_zero.mpr hR).trans hs.1, hs.2⟩
  obtain ⟨hK, hKD, hint, hfront, -, hcore⟩ :=
    htrunc D (he.trans (min_le_right _ _)) s
      ⟨(neg_lt_zero.mpr hR).trans hs.1, hs.2⟩
  let K := D.closed_core ∪ closure (D.end_neck.region (-D.epsilon⁻¹) s)
  have htail' : D.end_neck.region (s - delta) D.epsilon⁻¹ ⊆ U := by
    intro y hy
    exact htaila ⟨hy.1, (hat.trans htl).trans hy.2.1, hy.2.2⟩
  have hcollar : D.end_neck.region (s - delta) (s + delta) ⊆ U :=
    fun _ hy => htail' ⟨hy.1, hy.2.1, hy.2.2.trans hhi⟩
  have hxK : x ∈ interior K := by
    rw [hint]
    rcases hxt with hc | ht
    · exact Or.inl hc
    · exact Or.inr ⟨ht.1, ht.2.1, ht.2.2.trans (by linarith)⟩
  have hunion : D.carrier ∩ (U : Set M) = ((U : Set M) ∩ interior K) ∪
      D.end_neck.region (s - delta) D.epsilon⁻¹ := by
    rw [hint]
    apply Subset.antisymm
    · rintro y ⟨hyD, hyU⟩
      rcases D.carrier_eq_closed_core_union_end ▸ hyD with hc | hend
      · exact Or.inl ⟨hyU, Or.inl hc⟩
      · have hh := (D.end_neck.coordinate_inverse_mem y hend).2
        rw [D.end_neck_epsilon] at hh
        by_cases hys : (D.end_neck.coordinate_inverse y).2 < s
        · exact Or.inl ⟨hyU, Or.inr ⟨hend, hh.1, hys⟩⟩
        · exact Or.inr ⟨hend, by linarith [le_of_not_gt hys], hh.2⟩
    · rintro y (⟨hyU, hc | hend⟩ | hend)
      · exact ⟨D.closed_core_subset_carrier hc, hyU⟩
      · exact ⟨D.end_neck_subset hend.1, hyU⟩
      · exact ⟨D.end_neck_subset hend.1, htail' hend⟩
  have hinter : ((U : Set M) ∩ interior K) ∩
      D.end_neck.region (s - delta) D.epsilon⁻¹ =
        D.end_neck.region (s - delta) s := by
    rw [hint]
    apply Subset.antisymm
    · rintro y ⟨⟨-, hc | hend⟩, ht⟩
      · exact (disjoint_left.mp D.disjoint_closed_core_end hc ht.1).elim
      · exact ⟨hend.1, ht.2.1, hend.2.2⟩
    · intro y hy
      have hh := (D.end_neck.coordinate_inverse_mem y hy.1).2
      rw [D.end_neck_epsilon] at hh
      have ht : y ∈ D.end_neck.region (s - delta) D.epsilon⁻¹ :=
        ⟨hy.1, hy.2.1, hh.2⟩
      exact ⟨⟨htail' ht, Or.inr ⟨hy.1, hh.1, hy.2.2⟩⟩, ht⟩
  have hescape : ∀ L : Set M, IsCompact L → L ⊆ U →
      ¬ (U : Set M) ∩ interior K ⊆ L ∧ ¬ (U : Set M) \ K ⊆ L := by
    have hxout := ((C.carrier_open.union U.isOpen).frontier_eq ▸ hxfront).2
    have hxcl : x ∈ closure (U : Set M) := by
      have hx := frontier_subset_closure hxfront
      have hCU : C.carrier ∪ (U : Set M) = C.closed_core ∪ (U : Set M) := by
        rw [C.carrier_eq_closed_core_union_end, union_assoc, union_eq_right.mpr hend]
      rw [hCU, closure_union, C.isClosed_closed_core.closure_eq] at hx
      exact hx.resolve_left (fun h => hxout (Or.inl (C.closed_core_subset_carrier h)))
    have hxside : x ∈ closure ((U : Set M) ∩ interior K) := by
      apply mem_closure_iff.mpr
      intro V hV hxV
      obtain ⟨y, hy, hyU⟩ := mem_closure_iff.mp hxcl (V ∩ interior K)
        (hV.inter isOpen_interior) ⟨hxV, hxK⟩
      exact ⟨y, hy.1, hyU, hy.2⟩
    have hcB : C.boundary_neck.center ∈ C.boundary_sphere :=
      C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
    have hcCore := C.boundary_subset_closed_core hcB
    have hcout : C.boundary_neck.center ∉ U :=
      fun hc => disjoint_left.mp hfirst hcCore hc
    have hcK : C.boundary_neck.center ∉ K :=
      fun hc => disjoint_left.mp hCD hcCore (hKD hc)
    have hccl : C.boundary_neck.center ∈ closure (U : Set M) :=
      closure_mono ((C.end_neck.region_subset_carrier _ _).trans hend)
        (C.boundary_subset_negative_end_closure hcB)
    have hcside : C.boundary_neck.center ∈ closure ((U : Set M) \ K) := by
      apply mem_closure_iff.mpr
      intro V hV hcV
      obtain ⟨y, hy, hyU⟩ := mem_closure_iff.mp hccl (V ∩ Kᶜ)
        (hV.inter hK.isClosed.isOpen_compl) ⟨hcV, hcK⟩
      exact ⟨y, hy.1, hyU, hy.2⟩
    intro L hL hLU
    constructor
    · intro hsub
      exact hxout (Or.inr (hLU (hL.isClosed.closure_eq ▸ closure_mono hsub hxside)))
    · intro hsub
      exact hcout (hLU (hL.isClosed.closure_eq ▸ closure_mono hsub hcside))
  have hlo' : -D.epsilon⁻¹ < s - delta := (neg_lt_zero.mpr hR).trans hlo
  obtain ⟨hcA, hcB, hcover, -, -⟩ := D.truncated_sides_components U.isOpen
    T.isConnected_carrier hK.isClosed hdelta hlo' hhi hcollar hint hfront
  have hloNeck : -D.end_neck.epsilon⁻¹ < s - delta := by rwa [D.end_neck_epsilon]
  have hhiNeck : s + delta < D.end_neck.epsilon⁻¹ := by rwa [D.end_neck_epsilon]
  obtain ⟨c, hcs, hct, hc, hci, hcval⟩ := D.end_neck.exists_slice_collar hloNeck hhiNeck
  obtain ⟨E, -⟩ := D.end_neck.exists_unit_to_real_cylinder
  let T' := E.symm.trans (T.toDiffeomorph U)
  have hS : range (fun q : UnitTwoSphere => c (q, 0)) =
      range (fun q : UnitTwoSphere => D.end_neck.coordinate_map (q, s)) := by
    congr 1
    funext q
    simpa only [add_zero] using hcval (q, 0)
  obtain ⟨eta, heta, hetaDelta, F, hF⟩ :=
    Poincare.exists_essential_sphere_collar_extension_in_open U T' hdelta c hcs
      (hct ▸ hcollar) hc hci ((U : Set M) ∩ interior K) ((U : Set M) \ K)
      (U.isOpen.inter isOpen_interior) (U.isOpen.inter hK.isClosed.isOpen_compl) hcA hcB
      (disjoint_left.mpr fun _ hy hz => hz.2 (interior_subset hy.2))
      (by rw [hS, ← hfront]; exact hcover) hescape
  have hFval (p : RoundCylinderSpace) (hp : |p.2| < eta) :
      (F p : M) = D.end_neck.coordinate_map (p.1, s + p.2) :=
    (hF p hp).trans (hcval p)
  have hFzero : range (fun q : UnitTwoSphere => (F (q, 0) : M)) = frontier K := by
    rw [hfront]
    congr 1
    funext q
    simpa only [add_zero] using hFval (q, 0) (by simpa using heta)
  let q := (D.end_neck.coordinate_inverse D.end_neck.center).1
  let p₀ : RoundCylinderSpace := (q, -eta / 2)
  have hp₀ : p₀.2 < 0 := by dsimp [p₀]; linarith
  have hpeta : |p₀.2| < eta := by rw [abs_of_neg hp₀]; dsimp [p₀]; linarith
  have hseed : (F p₀ : M) ∈ (U : Set M) ∩ interior K := by
    have hdom : (q, s + p₀.2) ∈ D.end_neck.cylinderDomain := by
      rw [EpsilonNeck.cylinderDomain, D.end_neck_epsilon]
      refine ⟨mem_univ _, ?_, ?_⟩ <;> dsimp [p₀] <;> linarith
    have hr : (F p₀ : M) ∈ D.end_neck.region (s - delta) s := by
      rw [hFval p₀ hpeta]
      refine ⟨D.end_neck.coordinate_map_mem hdom, ?_⟩
      rw [D.end_neck.coordinate_inverse_coordinate_map hdom]
      constructor <;> dsimp [p₀] <;> linarith
    exact (hinter.ge hr).1
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  obtain ⟨-, hright⟩ := Poincare.Topology.cylinder_sides_of_negative_witness U
    F.toHomeomorph (U.isOpen.inter isOpen_interior) (U.isOpen.inter hK.isClosed.isOpen_compl)
    hcA.isPreconnected (disjoint_left.mpr fun _ hy hz => hz.2 (interior_subset hy.2))
    (hFzero.symm ▸ hcover) hp₀ hseed
  have hFside (p : RoundCylinderSpace) : (F p : M) ∈ K ↔ p.2 ≤ 0 := by
    have h : (F p : M) ∉ K ↔ 0 < p.2 :=
      (and_iff_right (F p).property).symm.trans (hright p)
    simpa only [not_not, not_lt] using not_congr h
  obtain ⟨r, G, hr, -, hGaff, hGside⟩ :=
    D.end_neck.exists_affine_neck_coordinates (fun _ => s) contMDiff_const (fun _ => hs')
  have hG (p : RoundCylinderSpace) (hp : |p.2| < r) :
      (G p : M) = D.end_neck.coordinate_map (p.1, s + p.2) := by
    have h := D.end_neck.coordinate_map_coordinate_inverse (G p).property
    rw [hGaff p hp] at h
    exact h.symm
  have hpos (p : RoundCylinderSpace) (hp : 0 < p.2) :
      (G p : M) ∈ D.end_neck.region s D.epsilon⁻¹ := by
    refine ⟨(G p).property, ?_, ?_⟩
    · exact lt_of_not_ge fun h => (not_le_of_gt hp) ((hGside p).mp h)
    · simpa only [D.end_neck_epsilon] using
        (D.end_neck.coordinate_inverse_mem _ (G p).property).2.2
  have havoid : Disjoint K (D.end_neck.region s D.epsilon⁻¹) := by
    have hcl : closure (D.end_neck.region (-D.epsilon⁻¹) s) ⊆
        (D.end_neck.region s D.epsilon⁻¹)ᶜ := by
      apply closure_minimal _ (D.end_neck.isOpen_region s D.epsilon⁻¹).isClosed_compl
      exact fun _ hy hz => lt_asymm hy.2.2 hz.2.1
    apply disjoint_left.mpr
    intro y hy hz
    rcases hy with hc | hend
    · exact disjoint_left.mp D.disjoint_closed_core_end hc hz.1
    · exact hcl hend hz
  obtain ⟨W, P, -, hW⟩ := Poincare.exists_pasted_cylinder U D.end_neck.carrierOpen
    F G (min eta r) (lt_min heta hr)
    (fun p hp => (hFval p (hp.trans_le (min_le_left _ _))).trans
      (hG p (hp.trans_le (min_le_right _ _))).symm)
    (fun p q hp hq heq => disjoint_left.mp havoid ((hFside p).mpr hp)
      (heq.symm ▸ hpos q hq))
  have hWexact : (W : Set M) = D.carrier ∩ (U : Set M) := by
    rw [hW]
    apply Subset.antisymm
    · rintro y (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · exact ⟨hKD ((hFside p).mpr hp), (F p).property⟩
      · have hy := hpos p hp
        exact ⟨D.end_neck_subset hy.1, htail' ⟨hy.1, by linarith [hy.2.1], hy.2.2⟩⟩
    · intro y hy
      by_cases hyK : y ∈ K
      · left
        obtain ⟨p, hp⟩ := F.surjective ⟨y, hy.2⟩
        have hp' : (F p : M) = y := congrArg Subtype.val hp
        refine ⟨p, (hFside p).mp ?_, congrArg Subtype.val hp⟩
        change (F p : M) ∈ K
        rw [hp']
        exact hyK
      · right
        have hytail : y ∈ D.end_neck.region (s - delta) D.epsilon⁻¹ :=
          (hunion.le hy).resolve_left fun hi => hyK (interior_subset hi.2)
        have hygt : s < (D.end_neck.coordinate_inverse y).2 := by
          by_contra hn
          rcases lt_or_eq_of_le (le_of_not_gt hn) with hl | heq
          · exact hyK (interior_subset (hinter.ge ⟨hytail.1, hytail.2.1, hl⟩).1.2)
          · have hys : y ∈ frontier K := by
              rw [hfront]
              refine ⟨(D.end_neck.coordinate_inverse y).1, ?_⟩
              rw [← heq]
              exact D.end_neck.coordinate_map_coordinate_inverse hytail.1
            exact hyK (hK.isClosed.frontier_subset hys)
        obtain ⟨p, hp⟩ := G.surjective ⟨y, hytail.1⟩
        have hp' : (G p : M) = y := congrArg Subtype.val hp
        refine ⟨p, ?_, congrArg Subtype.val hp⟩
        have hnot : ¬ (D.end_neck.coordinate_inverse (G p)).2 ≤ s := by
          rw [hp']
          exact not_le.mpr hygt
        exact lt_of_not_ge fun h => hnot ((hGside p).mpr h)
  have model : OpenCylinderModel (W : Set M) :=
    OpenCylinderModel.ofDiffeomorph W (E.trans P)
      (D.end_neck.coordinate_inverse D.end_neck.center).1
  exact ⟨hWexact ▸ model⟩

end PoincareConjecture.CompactKappa
