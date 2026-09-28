import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Regions
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Noncompact
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Tails













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

namespace OpenCylinderModel

private theorem axial_sphere_mem {U : Set M} (T : OpenCylinderModel U)
    {x : M} (hx : x ∈ U) {a : ℝ} (ha : (T.inverse x).2 = a) :
    x ∈ T.coordinate '' (univ ×ˢ ({a} : Set ℝ)) :=
  ⟨T.inverse x, ⟨mem_univ _, ha⟩, T.right_inverse hx⟩

private theorem below_of_preconnected {U S : Set M} (T : OpenCylinderModel U)
    (hS : IsPreconnected S) (hSU : S ⊆ U) {a : ℝ}
    (hdis : Disjoint S (T.coordinate '' (univ ×ˢ ({a} : Set ℝ))))
    {p : M} (hp : p ∈ S) (hpa : (T.inverse p).2 < a) :
    ∀ x ∈ S, (T.inverse x).2 < a := by
  intro x hx
  by_contra hxa
  obtain ⟨y, hy, hya⟩ := hS.intermediate_value hp hx
    (T.inverse_smooth.continuousOn.snd.mono hSU) ⟨hpa.le, le_of_not_gt hxa⟩
  exact disjoint_left.mp hdis hy (T.axial_sphere_mem (hSU hy) hya)

private theorem above_of_preconnected {U S : Set M} (T : OpenCylinderModel U)
    (hS : IsPreconnected S) (hSU : S ⊆ U) {a : ℝ}
    (hdis : Disjoint S (T.coordinate '' (univ ×ˢ ({a} : Set ℝ))))
    {p : M} (hp : p ∈ S) (hpa : a < (T.inverse p).2) :
    ∀ x ∈ S, a < (T.inverse x).2 := by
  intro x hx
  by_contra hxa
  obtain ⟨y, hy, hya⟩ := hS.intermediate_value hx hp
    (T.inverse_smooth.continuousOn.snd.mono hSU) ⟨le_of_not_gt hxa, hpa.le⟩
  exact disjoint_left.mp hdis hy (T.axial_sphere_mem (hSU hy) hya)

private theorem exists_below_outside_compact {U K : Set M}
    (T : OpenCylinderModel U) (hK : IsCompact K) (hKU : K ⊆ U)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ x ∈ U, (T.inverse x).2 < a ∧ x ∉ K := by
  obtain ⟨b, hb, hdis, _⟩ := T.exists_tails_disjoint_of_isCompact hK hKU
  have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨hb.1, by linarith [hb.2]⟩
  have hab : min a b ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min ha.1 hb.1, (min_le_left _ _).trans_lt ha.2⟩
  obtain ⟨x, hx⟩ := (T.isConnected_tail false hab).nonempty
  have hx' := (T.mem_tail_iff false hab).mp hx
  refine ⟨x, hx'.1, hx'.2.trans_le (min_le_left _ _), ?_⟩
  exact fun h => disjoint_left.mp hdis
    ((T.mem_tail_iff false hb').mpr ⟨hx'.1, hx'.2.trans_le (min_le_right _ _)⟩) h

private theorem exists_above_outside_compact {U K : Set M}
    (T : OpenCylinderModel U) (hK : IsCompact K) (hKU : K ⊆ U)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ x ∈ U, a < (T.inverse x).2 ∧ x ∉ K := by
  obtain ⟨b, hb, _, hdis, _⟩ := T.exists_tails_disjoint_of_isCompact hK hKU
  have hb' : 1 - b ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hb.1, hb.2]
  have hab : max a (1 - b) ∈ Ioo (0 : ℝ) 1 :=
    ⟨ha.1.trans_le (le_max_left _ _), max_lt ha.2 hb'.2⟩
  obtain ⟨x, hx⟩ := (T.isConnected_tail true hab).nonempty
  have hx' := (T.mem_tail_iff true hab).mp hx
  refine ⟨x, hx'.1, (le_max_left _ _).trans_lt hx'.2, ?_⟩
  exact fun h => disjoint_left.mp hdis
    ((T.mem_tail_iff true hb').mpr ⟨hx'.1, (le_max_right _ _).trans_lt hx'.2⟩) h

private theorem disjoint_frontier_of_compact_complement [T2Space M]
    {U V : Set M} (T : OpenCylinderModel U) (W : OpenCylinderModel V)
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hK : IsCompact (U \ V)) : Disjoint (frontier V) U := by
  apply disjoint_left.mpr
  intro x hx hxU
  have hxnot : x ∉ V := (hV.frontier_eq ▸ hx).2
  have hxK : x ∈ U \ V := ⟨hxU, hxnot⟩
  obtain ⟨a, ha, hneg, hpos, _⟩ :=
    T.exists_tails_disjoint_of_isCompact hK sdiff_subset
  have haone : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  have hacomp : 1 - a ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [ha.1, ha.2]
  let l := a / 2
  let r := 1 - a / 2
  have hl : l ∈ Ioo (0 : ℝ) 1 := by dsimp [l]; constructor <;> linarith [ha.1, ha.2]
  have hr : r ∈ Ioo (0 : ℝ) 1 := by dsimp [r]; constructor <;> linarith [ha.1, ha.2]
  have hlr : l < r := by dsimp [l, r]; linarith [ha.2]
  let S := T.coordinate '' (univ ×ˢ ({l} : Set ℝ)) ∪
    T.coordinate '' (univ ×ˢ ({r} : Set ℝ))
  have hSc : IsCompact S := by
    apply IsCompact.union
    · simpa only [Icc_self] using T.isCompact_coordinate_slab hl.1 hl.2
    · simpa only [Icc_self] using T.isCompact_coordinate_slab hr.1 hr.2
  have hSV : S ⊆ V := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · have hz' : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 := by
        exact ⟨mem_univ _, hz.2 ▸ hl⟩
      have hyU := T.coordinate_mem hz'
      by_contra hyV
      apply disjoint_left.mp hneg _ ⟨hyU, hyV⟩
      apply (T.mem_tail_iff false haone).mpr
      refine ⟨hyU, ?_⟩
      rw [T.left_inverse hz', hz.2]
      dsimp [l]
      linarith [ha.1]
    · have hz' : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 := by
        exact ⟨mem_univ _, hz.2 ▸ hr⟩
      have hyU := T.coordinate_mem hz'
      by_contra hyV
      apply disjoint_left.mp hpos _ ⟨hyU, hyV⟩
      apply (T.mem_tail_iff true hacomp).mpr
      refine ⟨hyU, ?_⟩
      rw [T.left_inverse hz', hz.2]
      dsimp [r]
      linarith [ha.1]
  obtain ⟨b, hb, hbneg, hbpos, hL, hcover⟩ :=
    W.exists_tails_disjoint_of_isCompact hSc hSV
  have hbone : b ∈ Ioo (0 : ℝ) 1 := ⟨hb.1, by linarith [hb.2]⟩
  have hbcomp : 1 - b ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hb.1, hb.2]
  let L := W.coordinate '' (univ ×ˢ Icc b (1 - b))
  have hLV : L ⊆ V := W.coordinate_slab_subset hb.1 hbcomp.2
  have hLU : L ⊆ U := hLV.trans hVU
  have hKL : IsCompact ((U \ V) ∪ L) := hK.union hL
  have hKLU : (U \ V) ∪ L ⊆ U := union_subset sdiff_subset hLU
  obtain ⟨p, hpU, hpbelow, hpout⟩ := T.exists_below_outside_compact hKL hKLU hl
  obtain ⟨q, hqU, hqabove, hqout⟩ := T.exists_above_outside_compact hKL hKLU hr
  have hpV : p ∈ V := by by_contra h; exact hpout (Or.inl ⟨hpU, h⟩)
  have hqV : q ∈ V := by by_contra h; exact hqout (Or.inl ⟨hqU, h⟩)
  have hpends : p ∈ W.tail false b ∪ W.tail true (1 - b) := by
    by_contra h
    exact hpout (Or.inr (hcover ⟨hpV, h⟩))
  have hqends : q ∈ W.tail false b ∪ W.tail true (1 - b) := by
    by_contra h
    exact hqout (Or.inr (hcover ⟨hqV, h⟩))
  have hbelow₀ := T.below_of_preconnected (p := p)
    (W.isConnected_tail false hbone).isPreconnected
    ((W.tail_subset false hbone).trans hVU) (hbneg.mono_right subset_union_left)
  have hbelow₁ := T.below_of_preconnected (p := p)
    (W.isConnected_tail true hbcomp).isPreconnected
    ((W.tail_subset true hbcomp).trans hVU) (hbpos.mono_right subset_union_left)
  have habove₀ := T.above_of_preconnected (p := q)
    (W.isConnected_tail false hbone).isPreconnected
    ((W.tail_subset false hbone).trans hVU) (hbneg.mono_right subset_union_right)
  have habove₁ := T.above_of_preconnected (p := q)
    (W.isConnected_tail true hbcomp).isPreconnected
    ((W.tail_subset true hbcomp).trans hVU) (hbpos.mono_right subset_union_right)
  have hmiddle : ∀ y ∈ V, l < (T.inverse y).2 → (T.inverse y).2 < r → y ∈ L := by
    intro y hy hyl hyr
    apply hcover
    refine ⟨hy, ?_⟩
    rcases hpends with hp | hp <;> rcases hqends with hq | hq
    · have h := hbelow₀ hp hpbelow q hq
      linarith
    · rintro (hy₀ | hy₁)
      · exact (hbelow₀ hp hpbelow y hy₀).not_gt hyl
      · exact (habove₁ hq hqabove y hy₁).not_gt hyr
    · rintro (hy₀ | hy₁)
      · exact (habove₀ hq hqabove y hy₀).not_gt hyr
      · exact (hbelow₁ hp hpbelow y hy₁).not_gt hyl
    · have h := hbelow₁ hp hpbelow q hq
      linarith
  have hxlow : l < (T.inverse x).2 := by
    have hxa : a ≤ (T.inverse x).2 := by
      by_contra h
      exact disjoint_left.mp hneg
        ((T.mem_tail_iff false haone).mpr ⟨hxU, lt_of_not_ge h⟩) hxK
    dsimp [l]
    linarith [ha.1]
  have hxhigh : (T.inverse x).2 < r := by
    have hxa : (T.inverse x).2 ≤ 1 - a := by
      by_contra h
      exact disjoint_left.mp hpos
        ((T.mem_tail_iff true hacomp).mpr ⟨hxU, lt_of_not_ge h⟩) hxK
    dsimp [r]
    linarith [ha.1]
  have hcont := T.inverse_smooth.continuousOn.snd.continuousAt (hU.mem_nhds hxU)
  have hnhds : {y | l < (T.inverse y).2 ∧ (T.inverse y).2 < r} ∈ 𝓝 x :=
    hcont (isOpen_Ioo.mem_nhds ⟨hxlow, hxhigh⟩)
  have hxout : x ∉ L := fun h => hxnot (hLV h)
  obtain ⟨y, hy, hyV⟩ := mem_closure_iff_nhds.mp hx.1 _
    (Filter.inter_mem hnhds (hL.isClosed.isOpen_compl.mem_nhds hxout))
  exact hy.2 (hmiddle y hyV hy.1.1 hy.1.2)



theorem eq_of_subset_isCompact_complement [T2Space M]
    {U V : Set M} (T : OpenCylinderModel U) (W : OpenCylinderModel V)
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hK : IsCompact (U \ V)) : V = U := by
  have hdis := T.disjoint_frontier_of_compact_complement W hU hV hVU hK
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp T.isConnected_carrier
  obtain ⟨p, hp⟩ := W.isConnected_carrier.nonempty
  have heq := (isClopen_preimage_val hV hdis).eq_univ ⟨⟨p, hVU hp⟩, hp⟩
  apply Subset.antisymm hVU
  intro x hx
  exact (show (⟨x, hx⟩ : U) ∈ Subtype.val ⁻¹' V from heq ▸ mem_univ _)

end OpenCylinderModel


theorem OpenCylinderModel.not_isCompact_carrier {U : Set M}
    (T : OpenCylinderModel U) : ¬ IsCompact U := by
  intro hU
  obtain ⟨a, ha, hdis, _⟩ := T.exists_tails_disjoint_of_isCompact hU Subset.rfl
  have haone : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  obtain ⟨x, hx⟩ := (T.isConnected_tail false haone).nonempty
  exact disjoint_left.mp hdis hx (T.tail_subset false haone hx)

variable [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem EpsilonTubeCertificate.not_whole_of_isCompact {X : Set M}
    (T : EpsilonTubeCertificate g X) (hcompact : IsCompact (univ : Set M)) :
    ¬ univ ⊆ T.carrier := by
  intro hwhole
  exact T.cylinder.not_isCompact_carrier
    (Set.eq_univ_of_univ_subset hwhole ▸ hcompact)



theorem CappedTubeCertificate.not_isCompact_carrier
    (T : CappedTubeCertificate g) : ¬ IsCompact T.carrier := by
  intro hcompact
  have hK : IsCompact (T.tube.carrier \ (T.cap.carrier ∩ T.tube.carrier)) := by
    convert hcompact.inter_right T.cap.carrier_open.isClosed_compl using 1
    ext x
    rw [T.carrier_eq_union]
    simp only [mem_sdiff, mem_inter_iff, mem_union, mem_compl_iff]
    tauto
  have hfull := T.tube.cylinder.eq_of_subset_isCompact_complement
    T.attachment.overlap_model T.tube.carrier_open
    (T.cap.carrier_open.inter T.tube.carrier_open) inter_subset_right hK
  have htube : T.tube.carrier ⊆ T.cap.carrier := by
    intro x hx
    exact ((Set.ext_iff.mp hfull x).mpr hx).1
  have hcarrier : T.carrier = T.cap.carrier := by
    rw [T.carrier_eq_union, union_eq_left.mpr htube]
  exact T.cap.not_isCompact_carrier (hcarrier ▸ hcompact)



theorem GlobalNeckCapConclusion.closed_or_fibration_of_isCompact
    {epsilon C : ℝ} (conclusion : GlobalNeckCapConclusion g epsilon C)
    (hcompact : IsCompact (univ : Set M)) :
    (∃ kind : ClosedComponentKind,
      Nonempty (ClosedComponentCertificate kind (univ : Set M)) ∧
      Nonempty (GlobalClosedShape g epsilon C (univ : Set M))) ∨
    (∃ T : SphereBundleCircleCertificate g (univ : Set M),
      T.epsilon = epsilon ∧ T.carrier = univ) := by
  cases conclusion with
  | closed Y kind component whole shape =>
      have hY := Set.eq_univ_of_univ_subset whole
      subst Y
      exact Or.inl ⟨kind, ⟨component⟩, ⟨shape⟩⟩
  | noncompact certificate =>
      rcases certificate.shape with ⟨cap, hcarrier, hepsilon, hconstant, hkind⟩ |
        ⟨T, hcarrier, hepsilon, htube, hconstant, hkind⟩
      · have hwhole := hcarrier.trans (Set.eq_univ_of_univ_subset certificate.whole)
        exact (cap.not_isCompact_carrier (hwhole ▸ hcompact)).elim
      · have hwhole := hcarrier.trans (Set.eq_univ_of_univ_subset certificate.whole)
        exact (T.not_isCompact_carrier (hwhole ▸ hcompact)).elim
  | tube T hepsilon hcarrier =>
      exact (T.not_whole_of_isCompact hcompact (by rw [hcarrier])).elim
  | fibration T hepsilon hcarrier =>
      exact Or.inr ⟨T, hepsilon, hcarrier⟩

end PoincareConjecture
