import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCuts

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

theorem CapCertificate.exists_later_lower_cut_containing_compact
    (C : CapCertificate g) {K : Set M}
    (hK : IsCompact K) (hKC : K ⊆ C.carrier)
    {d : ℝ} (hd : d ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    ∃ t ∈ Ioo d C.epsilon⁻¹,
      K ⊆ interior (C.carrier \ C.end_neck.region t C.epsilon⁻¹) := by
  let L := C.epsilon⁻¹
  let N := C.end_neck
  have hN : N.epsilon = C.epsilon := C.end_neck_epsilon
  change d ∈ Ioo (-L) L at hd
  let W : Ioo d L → Set M := fun t => C.closed_core ∪ N.region (-L) t
  let : Nonempty (Ioo d L) := ⟨⟨(d + L) / 2, by constructor <;> linarith [hd.2]⟩⟩
  have hret (t : Ioo d L) : (t : ℝ) ∈ Ioo (-L) L :=
    ⟨hd.1.trans t.property.1, t.property.2⟩
  have hWopen (t : Ioo d L) : IsOpen (W t) :=
    (C.end_neck_lower_cut_topology (hret t)).2.1
  have hcover : C.carrier ⊆ ⋃ t, W t := by
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · have hs := (N.coordinate_inverse_mem x hxN).2
      rw [hN] at hs
      have hm : max d (N.coordinate_inverse x).2 < L := max_lt hd.2 hs.2
      let t : Ioo d L := ⟨(max d (N.coordinate_inverse x).2 + L) / 2,
        by constructor <;> linarith [le_max_left d (N.coordinate_inverse x).2]⟩
      refine mem_iUnion.mpr ⟨t, Or.inr ?_⟩
      refine ⟨hxN, hs.1, ?_⟩
      dsimp only [t]
      linarith [le_max_right d (N.coordinate_inverse x).2]
    · obtain ⟨t⟩ := (inferInstance : Nonempty (Ioo d L))
      refine mem_iUnion.mpr ⟨t, Or.inl ?_⟩
      rw [C.closed_core_eq_complement_end]
      exact ⟨hx, hxN⟩
  have hdir : Directed (· ⊆ ·) W := by
    intro a b
    let t : Ioo d L := ⟨max (a : ℝ) b,
      lt_max_iff.mpr (Or.inl a.property.1), max_lt a.property.2 b.property.2⟩
    refine ⟨t, ?_, ?_⟩
    · rintro x (hx | hx)
      · exact Or.inl hx
      · exact Or.inr ⟨hx.1, hx.2.1, hx.2.2.trans_le (le_max_left _ _)⟩
    · rintro x (hx | hx)
      · exact Or.inl hx
      · exact Or.inr ⟨hx.1, hx.2.1, hx.2.2.trans_le (le_max_right _ _)⟩
  obtain ⟨t, ht⟩ := hK.elim_directed_cover W hWopen (hKC.trans hcover) hdir
  refine ⟨t, t.property, ?_⟩
  rw [(C.end_neck_lower_cut_topology (hret t)).2.2.2.1]
  exact ht

theorem CapTubeAttachment.exists_cofinal_overlap_end
    {X : Set M} {C : CapCertificate g}
    {T : EpsilonTubeCertificate g X} {side : Bool}
    (A : CapTubeAttachment C T side) :
    IsCompact (C.carrier \ T.carrier) ∧
      ∃ omega : Bool,
        (∀ a ∈ Ioo (0 : ℝ) 1,
          ∃ s ∈ Ioo 0 C.epsilon⁻¹,
            C.end_neck.region s C.epsilon⁻¹ ⊆
              A.overlap_model.tail omega a) ∧
        (∀ s ∈ Ioo (0 : ℝ) C.epsilon⁻¹,
          ∃ a ∈ Ioo (0 : ℝ) 1,
            A.overlap_model.tail omega a ⊆
              C.end_neck.region s C.epsilon⁻¹) ∧
        (∀ a ∈ Ioo (0 : ℝ) 1,
          IsCompact (C.carrier \ A.overlap_model.tail omega a)) ∧
        (∀ K : Set M, IsCompact K → K ⊆ C.carrier →
          ∀ d ∈ Ioo (0 : ℝ) 1,
            ∃ a ∈ Ioo (0 : ℝ) 1,
              (if omega then d < a else a < d) ∧
              Disjoint K (A.overlap_model.tail omega a)) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L := C.epsilon⁻¹
  let N := C.end_neck
  let O := C.carrier ∩ T.carrier
  let B := A.overlap_model
  let h : M → ℝ := fun x => (B.inverse x).2
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have hN : N.epsilon = C.epsilon := C.end_neck_epsilon
  have hO : IsOpen O := C.carrier_open.inter T.carrier_open
  have hcont : ContinuousOn h O := B.inverse_smooth.continuousOn.snd
  have hmap {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
      B.coordinate z ∈ O := by
    have hm := (B.homeomorph (z.1, ⟨z.2, hz.2⟩)).property
    rwa [B.coordinate_eq] at hm
  have htail (omega : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (x : M) :
      x ∈ B.tail omega a ↔ x ∈ O ∧ (if omega then a < h x else h x < a) := by
    cases omega
    · simp only [OpenCylinderModel.tail, Bool.false_eq_true, if_false]
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzs : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
          ⟨mem_univ _, hz.2.1, hz.2.2.trans ha.2⟩
        refine ⟨hmap hzs, ?_⟩
        change (B.inverse (B.coordinate z)).2 < a
        rw [B.left_inverse hzs]
        exact hz.2.2
      · rintro ⟨hx, hxa⟩
        exact ⟨B.inverse x, ⟨mem_univ _, (B.inverse_mem x hx).2.1, hxa⟩,
          B.right_inverse hx⟩
    · simp only [OpenCylinderModel.tail, if_true]
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzs : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
          ⟨mem_univ _, ha.1.trans hz.2.1, hz.2.2⟩
        refine ⟨hmap hzs, ?_⟩
        change a < (B.inverse (B.coordinate z)).2
        rw [B.left_inverse hzs]
        exact hz.2.1
      · rintro ⟨hx, hxa⟩
        exact ⟨B.inverse x, ⟨mem_univ _, hxa, (B.inverse_mem x hx).2.2⟩,
          B.right_inverse hx⟩
  have htailOpen (omega : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
      IsOpen (B.tail omega a) := by
    cases omega
    · have heq : B.tail false a = O ∩ h ⁻¹' Iio a := by
        ext x
        exact htail false ha x
      rw [heq]
      exact hcont.isOpen_inter_preimage hO isOpen_Iio
    · have heq : B.tail true a = O ∩ h ⁻¹' Ioi a := by
        ext x
        exact htail true ha x
      rw [heq]
      exact hcont.isOpen_inter_preimage hO isOpen_Ioi
  have hBconnected {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
      IsConnected (B.coordinate '' (univ ×ˢ Ioo a b)) := by
    apply (isConnected_univ.prod (isConnected_Ioo hab)).image
    exact B.coordinate_smooth.continuousOn.mono
      (fun _ hz => ⟨mem_univ _, ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩)
  have htailConnected (omega : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
      IsConnected (B.tail omega a) := by
    cases omega
    · exact hBconnected le_rfl ha.2.le ha.1
    · exact hBconnected ha.1.le le_rfl ha.2
  have hslab {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
      IsCompact (B.coordinate '' (univ ×ˢ Icc a b)) ∧
        B.coordinate '' (univ ×ˢ Icc a b) ⊆ O := by
    have hdom : (univ : Set UnitTwoSphere) ×ˢ Icc a b ⊆ univ ×ˢ Ioo (0 : ℝ) 1 :=
      fun _ hz => ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
    refine ⟨(isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (B.coordinate_smooth.continuousOn.mono hdom), ?_⟩
    rintro x ⟨z, hz, rfl⟩
    exact hmap (hdom hz)
  have hcapConnected {s : ℝ} (hs : s ∈ Ioo 0 L) : IsConnected (N.region s L) := by
    have hdom : univ ×ˢ Ioo s L ⊆ N.cylinderDomain := by
      intro z hz
      rw [EpsilonNeck.cylinderDomain, hN]
      exact ⟨mem_univ _, (neg_lt_zero.mpr hL).trans (hs.1.trans hz.2.1), hz.2.2⟩
    have heq : N.coordinate_map '' (univ ×ˢ Ioo s L) = N.region s L := by
      apply Subset.antisymm
      · rintro x ⟨z, hz, rfl⟩
        refine ⟨N.coordinate_map_mem (hdom hz), ?_⟩
        rw [N.coordinate_inverse_map z (hdom hz).2]
        exact hz.2
      · intro x hx
        exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, N.coordinate_map_inverse hx.1⟩
    rw [← heq]
    exact (isConnected_univ.prod (isConnected_Ioo hs.2)).image _
      (N.coordinate_map_smooth.continuousOn.mono hdom)
  have havoidCompact {K : Set M} (hK : IsCompact K) (hKC : K ⊆ C.carrier)
      {d : ℝ} (hd : d ∈ Ioo (-L) L) :
      ∃ t ∈ Ioo d L, Disjoint K (N.region t L) := by
    obtain ⟨t, ht, hKt⟩ := C.exists_later_lower_cut_containing_compact hK hKC hd
    refine ⟨t, ht, disjoint_left.mpr ?_⟩
    intro x hx hxN
    exact (interior_subset (hKt hx)).2 hxN
  obtain ⟨s₀, hs₀, hcapT⟩ := A.cap_tail
  change s₀ ∈ Ioo 0 L at hs₀
  have hs₀full : s₀ ∈ Ioo (-L) L := ⟨(neg_lt_zero.mpr hL).trans hs₀.1, hs₀.2⟩
  have hcapO {s : ℝ} (hs : s₀ ≤ s) : N.region s L ⊆ O := by
    intro x hx
    exact ⟨C.end_neck_subset hx.1, hcapT ⟨hx.1, hs.trans_lt hx.2.1, hx.2.2⟩⟩
  have hdiff : C.carrier \ T.carrier = (C.carrier \ N.region s₀ L) \ T.carrier := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨hx.1, fun hxN => hx.2 (hcapT hxN)⟩, hx.2⟩
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
  refine ⟨hdiff.symm ▸ (C.isCompact_end_neck_lower_cut hs₀full).diff T.carrier_open, ?_⟩
  let m : ℝ := 1 / 2
  have hm : m ∈ Ioo (0 : ℝ) 1 := by norm_num [m]
  obtain ⟨u, hu, havoid⟩ := havoidCompact (hslab hm.1 hm.2).1
    ((hslab hm.1 hm.2).2.trans inter_subset_left) hs₀full
  have hu0 : u ∈ Ioo 0 L := ⟨hs₀.1.trans hu.1, hu.2⟩
  have hune : ∀ x ∈ N.region u L, h x ≠ m := by
    intro x hx he
    have hxO := hcapO hu.1.le hx
    apply disjoint_left.mp havoid _ hx
    refine ⟨B.inverse x, ⟨mem_univ _, ?_, ?_⟩, B.right_inverse hxO⟩
    · exact he.ge
    · exact he.le
  obtain ⟨omega, hsign⟩ : ∃ omega : Bool,
      ∀ x ∈ N.region u L, if omega then m < h x else h x < m := by
    rcases (hcapConnected hu0).isPreconnected.mapsTo_Ioi_or_Iio
      (hcont.mono (hcapO hu.1.le)) hune with hp | hn
    · exact ⟨true, hp⟩
    · exact ⟨false, hn⟩
  have hforward : ∀ a ∈ Ioo (0 : ℝ) 1,
      ∃ s ∈ Ioo 0 L, N.region s L ⊆ B.tail omega a := by
    intro a ha
    have hSlab := hslab (lt_min ha.1 hm.1) (max_lt ha.2 hm.2)
    obtain ⟨v, hv, hdisj⟩ := havoidCompact hSlab.1
      (hSlab.2.trans inter_subset_left) ⟨(neg_lt_zero.mpr hL).trans hu0.1, hu.2⟩
    refine ⟨v, ⟨hu0.1.trans hv.1, hv.2⟩, ?_⟩
    intro x hx
    have hxu : x ∈ N.region u L := ⟨hx.1, hv.1.trans hx.2.1, hx.2.2⟩
    have hxO := hcapO hu.1.le hxu
    apply (htail omega ha x).mpr
    refine ⟨hxO, ?_⟩
    have hnot : ¬ (min a m ≤ h x ∧ h x ≤ max a m) := by
      intro hab
      exact disjoint_left.mp hdisj
        ⟨B.inverse x, ⟨mem_univ _, hab⟩, B.right_inverse hxO⟩ hx
    have hh := hsign x hxu
    cases omega
    · change h x < m at hh
      change h x < a
      by_contra hxa
      exact hnot ⟨(min_le_left _ _).trans (le_of_not_gt hxa),
        hh.le.trans (le_max_right _ _)⟩
    · change m < h x at hh
      change a < h x
      by_contra hxa
      exact hnot ⟨(min_le_right _ _).trans hh.le,
        (le_of_not_gt hxa).trans (le_max_left _ _)⟩
  have hcompact : ∀ a ∈ Ioo (0 : ℝ) 1, IsCompact (C.carrier \ B.tail omega a) := by
    intro a ha
    obtain ⟨s, hs, hsub⟩ := hforward a ha
    have heq : C.carrier \ B.tail omega a = (C.carrier \ N.region s L) \ B.tail omega a := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨hx.1, fun hxN => hx.2 (hsub hxN)⟩, hx.2⟩
      · intro hx
        exact ⟨hx.1.1, hx.2⟩
    rw [heq]
    exact (C.isCompact_end_neck_lower_cut
      ⟨(neg_lt_zero.mpr hL).trans hs.1, hs.2⟩).diff (htailOpen omega ha)
  have hreverse : ∀ s ∈ Ioo (0 : ℝ) L,
      ∃ a ∈ Ioo (0 : ℝ) 1, B.tail omega a ⊆ N.region s L := by
    intro s hs
    obtain ⟨v, hvlo, hvhi⟩ := exists_between (max_lt hs.2 hs₀.2)
    have hsv : s < v := (le_max_left _ _).trans_lt hvlo
    have hs₀v : s₀ < v := (le_max_right _ _).trans_lt hvlo
    have hv : v ∈ Ioo 0 L := ⟨hs.1.trans hsv, hvhi⟩
    have hvN : v ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [hN]
      exact ⟨(neg_lt_zero.mpr hL).trans hv.1, hv.2⟩
    let S := N.coordinate_map '' (univ ×ˢ ({v} : Set ℝ))
    have hmemS (x : M) : x ∈ S ↔ x ∈ N.carrier ∧ (N.coordinate_inverse x).2 = v := by
      constructor
      · rintro ⟨⟨q, r⟩, ⟨_, hr⟩, rfl⟩
        have hrv : r = v := hr
        subst r
        exact ⟨N.coordinate_map_mem ⟨mem_univ _, hvN⟩,
          congrArg Prod.snd (N.coordinate_inverse_map (q, v) hvN)⟩
      · rintro ⟨hx, he⟩
        exact ⟨N.coordinate_inverse x, ⟨mem_univ _, he⟩, N.coordinate_map_inverse hx⟩
    have hS : IsCompact S := by
      simpa only [S, Icc_self] using N.isCompact_coordinate_slab hvN.1 hvN.2
    have hSO : S ⊆ O := by
      intro x hx
      have hh := (hmemS x).mp hx
      apply hcapO le_rfl
      exact ⟨hh.1, by rw [hh.2]; exact hs₀v, by rw [hh.2]; exact hvhi⟩
    have hSne : S.Nonempty :=
      ⟨N.coordinate_map ((N.coordinate_inverse N.center).1, v),
        ⟨((N.coordinate_inverse N.center).1, v), ⟨mem_univ _, rfl⟩, rfl⟩⟩
    obtain ⟨a, ha, hdisj⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, Disjoint (B.tail omega a) S := by
      cases omega
      · obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hSne (hcont.mono hSO)
        have hxrange := (B.inverse_mem x₀ (hSO hx₀)).2
        change 0 < h x₀ ∧ h x₀ < 1 at hxrange
        have ha : h x₀ / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hxrange.1, hxrange.2]
        refine ⟨h x₀ / 2, ha, disjoint_left.mpr ?_⟩
        intro x hx hxS
        have hh := ((htail false ha x).mp hx).2
        have hminx : h x₀ ≤ h x := hmin hxS
        change h x < h x₀ / 2 at hh
        linarith [hxrange.1]
      · obtain ⟨x₀, hx₀, hmax⟩ := hS.exists_isMaxOn hSne (hcont.mono hSO)
        have hxrange := (B.inverse_mem x₀ (hSO hx₀)).2
        change 0 < h x₀ ∧ h x₀ < 1 at hxrange
        have ha : (h x₀ + 1) / 2 ∈ Ioo (0 : ℝ) 1 := by
          constructor <;> linarith [hxrange.1, hxrange.2]
        refine ⟨(h x₀ + 1) / 2, ha, disjoint_left.mpr ?_⟩
        intro x hx hxS
        have hh := ((htail true ha x).mp hx).2
        have hmaxx : h x ≤ h x₀ := hmax hxS
        change (h x₀ + 1) / 2 < h x at hh
        linarith
    let W := C.closed_core ∪ N.region (-L) v
    have hWopen : IsOpen W :=
      (C.end_neck_lower_cut_topology ⟨(neg_lt_zero.mpr hL).trans hv.1, hvhi⟩).2.1
    have hWR : Disjoint W (N.region v L) := by
      apply disjoint_left.mpr
      rintro x (hx | hx) hy
      · rw [C.closed_core_eq_complement_end] at hx
        exact hx.2 hy.1
      · exact (not_lt_of_gt hx.2.2) hy.2.1
    have hcover : B.tail omega a ⊆ W ∪ N.region v L := by
      intro x hx
      have hxO := ((htail omega ha x).mp hx).1
      by_cases hxN : x ∈ N.carrier
      · have hrange := (N.coordinate_inverse_mem x hxN).2
        rw [hN] at hrange
        rcases lt_trichotomy (N.coordinate_inverse x).2 v with hl | he | hr
        · exact Or.inl (Or.inr ⟨hxN, hrange.1, hl⟩)
        · exact False.elim (disjoint_left.mp hdisj hx ((hmemS x).mpr ⟨hxN, he⟩))
        · exact Or.inr ⟨hxN, hr, hrange.2⟩
      · apply Or.inl (Or.inl ?_)
        rw [C.closed_core_eq_complement_end]
        exact ⟨hxO.1, hxN⟩
    have hsub : B.tail omega a ⊆ N.region v L := by
      rcases IsPreconnected.subset_or_subset hWopen (N.isOpen_region v L) hWR hcover
        (htailConnected omega ha).isPreconnected with hw | hr
      · obtain ⟨r, hr, hrtail⟩ := hforward a ha
        obtain ⟨w, hwlo, hwhi⟩ := exists_between (max_lt hvhi hr.2)
        have hvw : v < w := (le_max_left _ _).trans_lt hwlo
        have hrw : r < w := (le_max_right _ _).trans_lt hwlo
        obtain ⟨x, hx⟩ := (hcapConnected ⟨hv.1.trans hvw, hwhi⟩).nonempty
        exact False.elim (disjoint_left.mp hWR
          (hw (hrtail ⟨hx.1, hrw.trans hx.2.1, hx.2.2⟩))
          ⟨hx.1, hvw.trans hx.2.1, hx.2.2⟩)
      · exact hr
    refine ⟨a, ha, ?_⟩
    intro x hx
    have hh := hsub hx
    exact ⟨hh.1, hsv.trans hh.2.1, hh.2.2⟩
  refine ⟨omega, hforward, hreverse, hcompact, ?_⟩
  intro K hK hKC d hd
  obtain ⟨r, hr, hKr⟩ := havoidCompact hK hKC ⟨neg_lt_zero.mpr hL, hL⟩
  obtain ⟨b, hb, hbr⟩ := hreverse r hr
  obtain ⟨a, ha, had, hab⟩ : ∃ a ∈ Ioo (0 : ℝ) 1,
      (if omega then d < a else a < d) ∧ (if omega then b < a else a < b) := by
    cases omega
    · refine ⟨min b d / 2, ?_, ?_, ?_⟩
      · constructor
        · exact half_pos (lt_min hb.1 hd.1)
        · linarith [min_le_left b d, hb.1, hb.2]
      · change min b d / 2 < d
        linarith [min_le_right b d, hd.1]
      · change min b d / 2 < b
        linarith [min_le_left b d, hb.1]
    · refine ⟨(max b d + 1) / 2, ?_, ?_, ?_⟩
      · constructor <;> linarith [le_max_left b d, max_lt hb.2 hd.2, hb.1]
      · change d < (max b d + 1) / 2
        linarith [le_max_right b d, max_lt hb.2 hd.2]
      · change b < (max b d + 1) / 2
        linarith [le_max_left b d, max_lt hb.2 hd.2]
  refine ⟨a, ha, had, disjoint_left.mpr ?_⟩
  intro x hxK hxA
  apply disjoint_left.mp hKr hxK (hbr ?_)
  apply (htail omega hb x).mpr
  have hh := (htail omega ha x).mp hxA
  refine ⟨hh.1, ?_⟩
  cases omega
  · exact lt_trans hh.2 hab
  · exact lt_trans hab hh.2

end PoincareConjecture
