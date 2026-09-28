import PoincareConjecture.Proofs.M25.Mathlib.CofinalCylinderEnd

set_option autoImplicit false

open Set Topology

namespace OpenPartialHomeomorph

theorem exists_cylinderTail_disjoint_compact_after_of_not_isCompact
    {K W : Type*} [TopologicalSpace K] [TopologicalSpace W]
    [ConnectedSpace K] [T2Space W] [WeaklyLocallyCompactSpace W]
    (e : OpenPartialHomeomorph (K × ℝ) W) {a b d : ℝ}
    (hsource : e.source = univ ×ˢ Ioo a b)
    (hcompact : ∀ t ∈ Ioo a b, IsCompact (e.cylinderTail b t)ᶜ)
    (hnoncompact : ¬ IsCompact (univ : Set W))
    {Q : Set W} (hQ : IsCompact Q) (hd : d ∈ Ioo a b) :
    ∃ t ∈ Ioo d b, Disjoint Q (e.cylinderTail b t) := by
  obtain ⟨V, hV, hinside⟩ := exists_compact_superset (hQ.union (hcompact d hd))
  have hfront : IsCompact (frontier V) :=
    hV.of_isClosed_subset isClosed_frontier hV.isClosed.frontier_subset
  have hfrontTail : frontier V ⊆ e.cylinderTail b d := by
    intro x hx
    by_contra hxTail
    exact hx.2 (hinside (Or.inr hxTail))
  obtain ⟨t, ht, hheight⟩ := e.exists_cylinder_height_lt_after hsource hfront
    (hfrontTail.trans (e.cylinderTail_subset_target hsource hd.1)) hd
  have htab : t ∈ Ioo a b := ⟨hd.1.trans ht.1, ht.2⟩
  have havoid : Disjoint (e.cylinderTail b t) (frontier V) := by
    apply disjoint_left.mpr
    intro x hx hxV
    exact (hheight x hxV).not_gt
      ((e.mem_cylinderTail_iff hsource htab.1 x).mp hx).2.1
  have hcover : e.cylinderTail b t ⊆ interior V ∪ Vᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior V
    · exact Or.inl hxi
    · refine Or.inr fun hxV => ?_
      exact disjoint_left.mp havoid hx ⟨subset_closure hxV, hxi⟩
  have hdisjoint : Disjoint (interior V) Vᶜ :=
    disjoint_left.mpr fun _ hx hy => hy (interior_subset hx)
  rcases (e.isConnected_cylinderTail hsource htab).isPreconnected.subset_or_subset
      isOpen_interior hV.isClosed.isOpen_compl hdisjoint hcover with hin | hout
  · exfalso
    apply hnoncompact
    have huniv : (univ : Set W) = (e.cylinderTail b t)ᶜ ∪ V := by
      apply Subset.antisymm
      · intro x _
        by_cases hx : x ∈ e.cylinderTail b t
        · exact Or.inr (interior_subset (hin hx))
        · exact Or.inl hx
      · exact subset_univ _
    rw [huniv]
    exact (hcompact t htab).union hV
  · refine ⟨t, ht, disjoint_left.mpr ?_⟩
    intro x hxQ hxTail
    exact hout hxTail (interior_subset (hinside (Or.inl hxQ)))

end OpenPartialHomeomorph
