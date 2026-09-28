import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapCoordinates












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D




theorem capCertificates_exists_buffered_cut_cover
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C1 C2 : ClosedModelCapData g)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier)) :
    let L := C1.epsilon⁻¹
    let Y := C1.carrier ∪ C2.carrier
    let N := C1
    let K : ℝ → Set M := fun t => C1.carrier \ N.region t L
    let V : ℝ → Set M := fun t => interior (K t)
    let W : ℝ → Set M := fun t => Y \ K t
    let Sigma : ℝ → Set M := fun t => N.coordinate_map '' (univ ×ˢ ({t} : Set ℝ))
    ∃ v ∈ Ioo (-L) L, (Y \ C2.carrier) ⊆ V v ∧
      ∀ a b : ℝ, v < a → a < b → b < L →
        IsOpen (V b) ∧ IsOpen (W a) ∧
        closure (W a) = Y \ V a ∧ interior (Y \ V a) = W a ∧
        IsCompact (Y \ V a) ∧ (Y \ V a) ⊆ C2.carrier ∧
        frontier (W a) = Sigma a ∧ frontier (V b) = Sigma b ∧
        V b ∪ W a = Y ∧ V b ∩ W a = N.region a b ∧
        N.region a b = N.coordinate_map '' (univ ×ˢ Ioo a b) ∧
        N.coordinate_map '' (univ ×ˢ Icc a b) ⊆ C2.carrier := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := C1.epsilon⁻¹
  let Y := C1.carrier ∪ C2.carrier
  let N := C1
  let K : ℝ → Set M := fun t => C1.carrier \ N.region t L
  let V : ℝ → Set M := fun t => interior (K t)
  let W : ℝ → Set M := fun t => Y \ K t
  let Sigma : ℝ → Set M := fun t => N.coordinate_map '' (univ ×ˢ ({t} : Set ℝ))
  change ∃ v ∈ Ioo (-L) L, (Y \ C2.carrier) ⊆ V v ∧
    ∀ a b : ℝ, v < a → a < b → b < L →
      IsOpen (V b) ∧ IsOpen (W a) ∧
      closure (W a) = Y \ V a ∧ interior (Y \ V a) = W a ∧
      IsCompact (Y \ V a) ∧ (Y \ V a) ⊆ C2.carrier ∧
      frontier (W a) = Sigma a ∧ frontier (V b) = Sigma b ∧
      V b ∪ W a = Y ∧ V b ∩ W a = N.region a b ∧
      N.region a b = N.coordinate_map '' (univ ×ˢ Ioo a b) ∧
      N.coordinate_map '' (univ ×ˢ Icc a b) ⊆ C2.carrier
  have hL : 0 < L := inv_pos.mpr C1.epsilon_pos
  have hYopen : IsOpen Y := C1.carrier_open.union C2.carrier_open
  have hYclosed : IsClosed Y := hcompact.isClosed
  have hheight (x : M) (hx : x ∈ N.end_chart.target) :
      (N.coordinate_inverse x).2 ∈ Ioo (-L) L := by
    exact (N.coordinate_inverse_mem x hx).2
  have hdata {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      closure (V t) = K t ∧ V t = C1.closed_core ∪ N.region (-L) t ∧
      frontier (V t) = Sigma t ∧ frontier (K t) = Sigma t := by
    obtain ⟨_, _, hcl, hi, hf, hfk, _⟩ := C1.end_neck_lower_cut_topology ht
    refine ⟨?_, hi, ?_, hfk⟩
    · change closure (interior (K t)) = K t
      rw [hi]
      exact hcl
    · change frontier (interior (K t)) = Sigma t
      rw [hi]
      exact hf
  have hmono {s t : ℝ} (hs : s ∈ Ioo (-L) L) (ht : t ∈ Ioo (-L) L)
      (hst : s ≤ t) : V s ⊆ V t := by
    rw [(hdata hs).2.1, (hdata ht).2.1]
    apply union_subset_union_right
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.trans_le hst⟩
  let : Nonempty (Ioo (-L) L) := ⟨⟨0, neg_lt_zero.mpr hL, hL⟩⟩
  have hcover : Y \ C2.carrier ⊆ ⋃ t : Ioo (-L) L, V (t : ℝ) := by
    intro x hx
    have hxC : x ∈ C1.carrier := hx.1.resolve_right hx.2
    by_cases hxN : x ∈ N.end_chart.target
    · let s := (N.coordinate_inverse x).2
      have hs : s ∈ Ioo (-L) L := hheight x hxN
      let t : Ioo (-L) L := ⟨(s + L) / 2, by constructor <;> linarith [hs.1, hs.2]⟩
      apply mem_iUnion.mpr
      refine ⟨t, ?_⟩
      rw [(hdata t.property).2.1]
      refine Or.inr ⟨hxN, hs.1, ?_⟩
      change s < (s + L) / 2
      linarith [hs.2]
    · let t : Ioo (-L) L := ⟨0, neg_lt_zero.mpr hL, hL⟩
      apply mem_iUnion.mpr
      refine ⟨t, ?_⟩
      rw [(hdata t.property).2.1]
      apply Or.inl
      rw [C1.closed_core_eq_complement_end]
      exact ⟨hxC, hxN⟩
  have hdirected : Directed (· ⊆ ·) (fun t : Ioo (-L) L => V (t : ℝ)) := by
    intro s t
    let w : Ioo (-L) L :=
      ⟨max (s : ℝ) (t : ℝ), s.property.1.trans_le (le_max_left _ _),
        max_lt s.property.2 t.property.2⟩
    exact ⟨w, hmono s.property w.property (le_max_left _ _),
      hmono t.property w.property (le_max_right _ _)⟩
  obtain ⟨v, hv⟩ := (hcompact.diff C2.carrier_open).elim_directed_cover
    (fun t : Ioo (-L) L => V (t : ℝ)) (fun _ => isOpen_interior) hcover hdirected
  refine ⟨v, v.property, hv, ?_⟩
  intro a b hva hab hb
  have ha : a ∈ Ioo (-L) L := ⟨v.property.1.trans hva, hab.trans hb⟩
  have hb' : b ∈ Ioo (-L) L := ⟨ha.1.trans hab, hb⟩
  obtain ⟨hclVa, hVa, _, hfrontKa⟩ := hdata ha
  obtain ⟨_, hVb, hfrontVb, _⟩ := hdata hb'
  have hKa : IsCompact (K a) := C1.isCompact_end_neck_lower_cut ha
  have hWopen : IsOpen (W a) := hYopen.sdiff hKa.isClosed
  have hWclosure : closure (W a) = Y \ V a := by
    apply Subset.antisymm
    · change closure (Y ∩ (K a)ᶜ) ⊆ Y ∩ (interior (K a))ᶜ
      simpa only [hYclosed.closure_eq, closure_compl] using
        (closure_inter_subset : closure (Y ∩ (K a)ᶜ) ⊆ closure Y ∩ closure (K a)ᶜ)
    · change Y ∩ (interior (K a))ᶜ ⊆ closure (Y ∩ (K a)ᶜ)
      simpa only [closure_compl] using (hYopen.inter_closure (t := (K a)ᶜ))
  have hWinterior : interior (Y \ V a) = W a := by
    change interior (Y ∩ (V a)ᶜ) = Y ∩ (K a)ᶜ
    rw [interior_inter, hYopen.interior_eq, interior_compl, hclVa]
  have hside : Y \ V a ⊆ C2.carrier := by
    intro x hx
    by_contra hxC
    exact hx.2 (hmono v.property ha hva.le (hv ⟨hx.1, hxC⟩))
  have hWfrontier : frontier (W a) = Sigma a := by
    calc
      frontier (W a) = (Y \ V a) \ (Y \ K a) := by
        rw [hWopen.frontier_eq, hWclosure]
      _ = K a \ V a := by
        ext x
        constructor
        · rintro ⟨⟨hxY, hxV⟩, hxW⟩
          refine ⟨?_, hxV⟩
          by_contra hxK
          exact hxW ⟨hxY, hxK⟩
        · rintro ⟨hxK, hxV⟩
          exact ⟨⟨Or.inl hxK.1, hxV⟩, fun hxW => hxW.2 hxK⟩
      _ = frontier (K a) := by rw [frontier, hKa.isClosed.closure_eq]
      _ = Sigma a := hfrontKa
  have hKV : K a ⊆ V b := by
    intro x hx
    rw [hVb]
    by_cases hxN : x ∈ N.end_chart.target
    · have hle : (N.coordinate_inverse x).2 ≤ a := by
        by_contra hnot
        exact hx.2 ⟨hxN, lt_of_not_ge hnot, (hheight x hxN).2⟩
      exact Or.inr ⟨hxN, (hheight x hxN).1, hle.trans_lt hab⟩
    · apply Or.inl
      rw [C1.closed_core_eq_complement_end]
      exact ⟨hx.1, hxN⟩
  have hVWcover : V b ∪ W a = Y := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl (interior_subset hx).1
      · exact hx.1
    · intro hx
      by_cases hxK : x ∈ K a
      · exact Or.inl (hKV hxK)
      · exact Or.inr ⟨hx, hxK⟩
  have hVWoverlap : V b ∩ W a = N.region a b := by
    ext x
    constructor
    · rintro ⟨hxV, hxW⟩
      rw [hVb] at hxV
      rcases hxV with hxC | hxN
      · rw [C1.closed_core_eq_complement_end] at hxC
        exact False.elim (hxW.2 ⟨hxC.1, fun hxT => hxC.2 hxT.1⟩)
      · have hxT : x ∈ N.region a L := by
          by_contra hnot
          exact hxW.2 ⟨C1.end_chart_target_subset hxN.1, hnot⟩
        exact ⟨hxN.1, hxT.2.1, hxN.2.2⟩
    · intro hx
      refine ⟨?_, Or.inl (C1.end_chart_target_subset hx.1), ?_⟩
      · rw [hVb]
        exact Or.inr ⟨hx.1, (hheight x hx.1).1, hx.2.2⟩
      · intro hxK
        exact hxK.2 ⟨hx.1, hx.2.1, (hheight x hx.1).2⟩
  have himage : N.region a b = N.coordinate_map '' (univ ×ˢ Ioo a b) := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, N.coordinate_map_inverse hx.1⟩
    · rintro x ⟨z, hz, rfl⟩
      have hzs : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
        exact ⟨ha.1.trans hz.2.1, hz.2.2.trans hb⟩
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hzs⟩, ?_⟩
      rw [N.coordinate_inverse_map z hzs]
      exact hz.2
  refine ⟨isOpen_interior, hWopen, hWclosure, hWinterior,
    hcompact.diff isOpen_interior, hside, hWfrontier, hfrontVb,
    hVWcover, hVWoverlap, himage, ?_⟩
  rintro x ⟨z, hz, rfl⟩
  have hzs : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    exact ⟨ha.1.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
  have hxN := N.coordinate_map_mem ⟨mem_univ _, hzs⟩
  apply hside
  refine ⟨Or.inl (C1.end_chart_target_subset hxN), ?_⟩
  intro hxV
  rw [hVa] at hxV
  rcases hxV with hxC | hxT
  · rw [C1.closed_core_eq_complement_end] at hxC
    exact hxC.2 hxN
  · have hlt := hxT.2.2
    rw [N.coordinate_inverse_map z hzs] at hlt
    exact (not_lt_of_ge hz.2.1) hlt

end PoincareConjecture.M25.Topology3D
