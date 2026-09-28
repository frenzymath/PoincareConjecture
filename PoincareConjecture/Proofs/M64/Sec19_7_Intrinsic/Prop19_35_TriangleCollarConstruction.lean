import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCollar





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff

namespace PoincareConjecture





theorem m64Intrinsic_exists_triangle_collar
    {base alpha beta : ℝ → AnnulusCoordinates}
    (hc : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {D A B : ℝ} (hci : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hbi : InjOn beta (Icc 0 B))
    (hcreg : ∀ t ∈ Ioo 0 D, deriv base t ≠ 0)
    (hareg : ∀ t ∈ Ioo 0 A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo 0 B, deriv beta t ≠ 0)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V)
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U)
    (C : M64IntrinsicTriangleCaps base alpha beta D A B U) :
    Nonempty (M64IntrinsicTriangleCollar C) := by
  have hcap := m64Intrinsic_triangle_caps_avoid_opposite_arcs C hbaseA hbaseB hsides hfront
  have h0D : C.radius 0 ≤ D := (C.radius_lt_left 0).le
  have h0A : C.radius 0 ≤ A := (C.radius_lt_right 0).le
  have h1D : C.radius 1 ≤ D := (C.radius_lt_left 1).le
  have h1B : C.radius 1 ≤ B := (C.radius_lt_right 1).le
  have h2A : C.radius 2 ≤ A := (C.radius_lt_left 2).le
  have h2B : C.radius 2 ≤ B := (C.radius_lt_right 2).le
  have havoidC : ∀ t ∈ Ioo 0 D,
      base t ∉ alpha '' Icc 0 A ∪ beta '' Icc 0 B := by
    rintro t ht (⟨s, hs, he⟩ | ⟨s, hs, he⟩)
    · exact ht.1.ne' (hbaseA t (Ioo_subset_Icc_self ht) s hs he.symm).1
    · exact ht.2.ne (hbaseB t (Ioo_subset_Icc_self ht) s hs he.symm).1
  have hcapC (e : Bool) : C.carrier (if e then 1 else 0) ∩ frontier U ⊆
      (fun s => base (if e then D - s else s)) '' Icc 0 (C.radius (if e then 1 else 0)) ∪
        (alpha '' Icc 0 A ∪ beta '' Icc 0 B) := by
    intro p hp
    cases e
    · rcases (C.frontier_contact 0).subset hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (image_mono (Icc_subset_Icc le_rfl h0A) h))
    · rcases (C.frontier_contact 1).subset hp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (image_mono (Icc_subset_Icc le_rfl h1B) h))
  obtain ⟨rev0, E0, h0Z, h0K, h0contact, h0cover⟩ :=
    m64Intrinsic_exists_finite_corner_arc_chain C (fun e => if e then 1 else 0)
      (by decide) (fun _ => false) hc hci hcreg
      ((isCompact_Icc.image ha.continuous).union (isCompact_Icc.image hb.continuous))
      havoidC hU hV hUV hfront hfV (C.compact 2).isClosed hcap.2.2.symm
      (by
        intro e
        cases e
        · exact C.radius_le_left_third 0
        · exact C.radius_le_left_third 1)
      (by
        intro e s
        cases e
        · exact C.first_axis 0 s
        · exact C.first_axis 1 s) hcapC
  let D0 : M64IntrinsicCornerArcCollar C (fun e => if e then 1 else 0) base D :=
    ⟨rev0, E0, h0contact, h0cover⟩
  have hfrontA : frontier U = alpha '' Icc 0 A ∪ (base '' Icc 0 D ∪ beta '' Icc 0 B) := by
    rw [hfront]
    ac_rfl
  have havoidA : ∀ t ∈ Ioo 0 A,
      alpha t ∉ base '' Icc 0 D ∪ beta '' Icc 0 B := by
    rintro t ht (⟨s, hs, he⟩ | ⟨s, hs, he⟩)
    · exact ht.1.ne' (hbaseA s hs t (Ioo_subset_Icc_self ht) he).2
    · exact ht.2.ne (hsides t (Ioo_subset_Icc_self ht) s hs he.symm).1
  have havoidZ1 : Disjoint (alpha '' Icc 0 A) (C.carrier 1 ∪ D0.bands) := by
    apply disjoint_left.mpr
    intro p hp hZ
    rcases hZ with h | h
    · exact disjoint_left.mp hcap.2.1 h hp
    · obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact disjoint_left.mp (h0K i) hi (Or.inl hp)
  have hcapA (e : Bool) : C.carrier (if e then 2 else 0) ∩ frontier U ⊆
      (fun s => alpha (if e then A - s else s)) '' Icc 0 (C.radius (if e then 2 else 0)) ∪
        (base '' Icc 0 D ∪ beta '' Icc 0 B) := by
    intro p hp
    cases e
    · rcases (C.frontier_contact 0).subset hp with h | h
      · exact Or.inr (Or.inl (image_mono (Icc_subset_Icc le_rfl h0D) h))
      · exact Or.inl h
    · rcases (C.frontier_contact 2).subset hp with h | h
      · exact Or.inl h
      · obtain ⟨s, hs, rfl⟩ := h
        exact Or.inr (Or.inr ⟨B - s,
          ⟨by linarith only [hs.2, h2B], by linarith only [hs.1]⟩, rfl⟩)
  obtain ⟨rev1, E1, h1Z, h1K, h1contact, h1cover⟩ :=
    m64Intrinsic_exists_finite_corner_arc_chain C (fun e => if e then 2 else 0)
      (by decide) (fun e => !e) ha hai hareg
      ((isCompact_Icc.image hc.continuous).union (isCompact_Icc.image hb.continuous))
      havoidA hU hV hUV hfrontA hfV ((C.compact 1).isClosed.union D0.bands_closed) havoidZ1
      (by
        intro e
        cases e
        · exact C.radius_le_right_third 0
        · exact C.radius_le_left_third 2)
      (by
        intro e s
        cases e
        · exact C.second_axis 0 s
        · exact C.first_axis 2 s) hcapA
  let D1 : M64IntrinsicCornerArcCollar C (fun e => if e then 2 else 0) alpha A :=
    ⟨rev1, E1, h1contact, h1cover⟩
  have hfrontB : frontier U = beta '' Icc 0 B ∪ (base '' Icc 0 D ∪ alpha '' Icc 0 A) := by
    rw [hfront]
    ac_rfl
  have havoidB : ∀ t ∈ Ioo 0 B,
      beta t ∉ base '' Icc 0 D ∪ alpha '' Icc 0 A := by
    rintro t ht (⟨s, hs, he⟩ | ⟨s, hs, he⟩)
    · exact ht.1.ne' (hbaseB s hs t (Ioo_subset_Icc_self ht) he).2
    · exact ht.2.ne (hsides s hs t (Ioo_subset_Icc_self ht) he).2
  have havoidZ2 : Disjoint (beta '' Icc 0 B) (C.carrier 0 ∪ (D0.bands ∪ D1.bands)) := by
    apply disjoint_left.mpr
    intro p hp hZ
    rcases hZ with h | (h | h)
    · exact disjoint_left.mp hcap.1 h hp
    · obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact disjoint_left.mp (h0K i) hi (Or.inr hp)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact disjoint_left.mp (h1K i) hi (Or.inr hp)
  have hcapB (e : Bool) : C.carrier (if e then 2 else 1) ∩ frontier U ⊆
      (fun s => beta (if e then B - s else s)) '' Icc 0 (C.radius (if e then 2 else 1)) ∪
        (base '' Icc 0 D ∪ alpha '' Icc 0 A) := by
    intro p hp
    cases e
    · rcases (C.frontier_contact 1).subset hp with h | h
      · obtain ⟨s, hs, rfl⟩ := h
        exact Or.inr (Or.inl ⟨D - s,
          ⟨by linarith only [hs.2, h1D], by linarith only [hs.1]⟩, rfl⟩)
      · exact Or.inl h
    · rcases (C.frontier_contact 2).subset hp with h | h
      · obtain ⟨s, hs, rfl⟩ := h
        exact Or.inr (Or.inr ⟨A - s,
          ⟨by linarith only [hs.2, h2A], by linarith only [hs.1]⟩, rfl⟩)
      · exact Or.inl h
  obtain ⟨rev2, E2, h2Z, _, h2contact, h2cover⟩ :=
    m64Intrinsic_exists_finite_corner_arc_chain C (fun e => if e then 2 else 1)
      (by decide) (fun _ => true) hb hbi hbreg
      ((isCompact_Icc.image hc.continuous).union (isCompact_Icc.image ha.continuous))
      havoidB hU hV hUV hfrontB hfV
      ((C.compact 0).isClosed.union (D0.bands_closed.union D1.bands_closed)) havoidZ2
      (by
        intro e
        cases e
        · exact C.radius_le_right_third 1
        · exact C.radius_le_right_third 2)
      (by
        intro e s
        cases e
        · exact C.second_axis 1 s
        · exact C.second_axis 2 s) hcapB
  let D2 : M64IntrinsicCornerArcCollar C (fun e => if e then 2 else 1) beta B :=
    ⟨rev2, E2, h2contact, h2cover⟩
  refine ⟨{
    baseArc := D0
    firstSide := D1
    secondSide := D2
    base_opposite := ?_
    first_opposite := ?_
    second_opposite := ?_
    base_first := ?_
    base_second := ?_
    first_second := ?_ }⟩
  · apply disjoint_left.mpr
    intro p hp hpc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact disjoint_left.mp (h0Z i) hi hpc
  · apply disjoint_left.mpr
    intro p hp hpc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact disjoint_left.mp (h1Z i) hi (Or.inl hpc)
  · apply disjoint_left.mpr
    intro p hp hpc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact disjoint_left.mp (h2Z i) hi (Or.inl hpc)
  · apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    exact disjoint_left.mp (h1Z i) hi (Or.inr hp)
  · apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    exact disjoint_left.mp (h2Z i) hi (Or.inr (Or.inl hp))
  · apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    exact disjoint_left.mp (h2Z i) hi (Or.inr (Or.inr hp))

end PoincareConjecture
