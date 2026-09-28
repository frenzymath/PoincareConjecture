import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.Balanced

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.DeepHorn

theorem not_isCompact_of_frontier_eq_cylinder_slice
    {M : Type*} [TopologicalSpace M] [T2Space M] {U K : Set M}
    (e : RoundCylinderSpace ≃ₜ U) (hK : K ⊆ U)
    (hfront : frontier K = (fun z : RoundCylinderSpace => (e z : M)) '' (univ ×ˢ {0}))
    (hint : (interior K).Nonempty) : ¬ IsCompact K := by
  intro hc
  let f : RoundCylinderSpace → M := fun z => e z
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hf_inj : Function.Injective f := fun _ _ h => e.injective (Subtype.ext h)
  let K' : Set U := Subtype.val ⁻¹' K
  have hc' : IsCompact K' := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    simpa only [K', image_preimage_eq_inter_range, Subtype.range_coe_subtype,
      ofPred_mem_eq, inter_eq_self_of_subset_left hK] using hc
  have hheight : IsCompact (Prod.snd '' (e.symm '' K')) :=
    (hc'.image e.symm.continuous).image continuous_snd
  obtain ⟨B, hB⟩ := hheight.bddAbove
  obtain ⟨A, hA⟩ := hheight.bddBelow
  have hside {V : Set RoundCylinderSpace} (hV : IsPreconnected V)
      (havoid : Disjoint V (univ ×ˢ ({0} : Set ℝ)))
      {x : M} (hx : x ∈ f '' V) (hxK : x ∈ interior K) : f '' V ⊆ K := by
    have havoid' : Disjoint (f '' V) (frontier K) := by
      rw [hfront]
      exact Disjoint.image havoid hf_inj.injOn (subset_univ _) (subset_univ _)
    have hcover : f '' V ⊆ interior K ∪ Kᶜ := by
      intro y hy
      by_cases hky : y ∈ K
      · left
        by_contra hn
        exact disjoint_left.mp havoid' hy ⟨hc.isClosed.closure_eq.symm ▸ hky, hn⟩
      · exact Or.inr hky
    rcases (hV.image f hf.continuousOn).subset_or_subset isOpen_interior
      hc.isClosed.isOpen_compl (disjoint_compl_right.mono_left interior_subset)
      hcover with h | h
    · exact h.trans interior_subset
    · exact False.elim (h hx (interior_subset hxK))
  obtain ⟨x, hx⟩ := hint
  let p := e.symm ⟨x, hK (interior_subset hx)⟩
  have hpx : f p = x := congrArg Subtype.val (e.apply_symm_apply _)
  have hnonzero : p.2 ≠ 0 := by
    intro hz
    have hxS : x ∈ frontier K := by
      rw [hfront]
      exact ⟨p, ⟨mem_univ _, hz⟩, hpx⟩
    exact hxS.2 hx
  rcases lt_or_gt_of_ne hnonzero with hn | hp
  · have hsub : f '' (univ ×ˢ Iio (0 : ℝ)) ⊆ K := by
      apply hside (isPreconnected_univ.prod isPreconnected_Iio) ?_ ⟨p, ⟨mem_univ _, hn⟩, hpx⟩ hx
      exact disjoint_left.mpr fun z hz hz' => ne_of_lt hz.2 hz'.2
    let t := min A 0 - 1
    have ht : t < 0 := by dsimp [t]; linarith [min_le_right A 0]
    have hmem : t ∈ Prod.snd '' (e.symm '' K') := by
      refine ⟨(p.1, t), ⟨e (p.1, t), ?_, e.symm_apply_apply _⟩, rfl⟩
      exact hsub ⟨(p.1, t), ⟨mem_univ _, ht⟩, rfl⟩
    have hbound := hA hmem
    dsimp [t] at hbound
    linarith [min_le_left A 0]
  · have hsub : f '' (univ ×ˢ Ioi (0 : ℝ)) ⊆ K := by
      apply hside (isPreconnected_univ.prod isPreconnected_Ioi) ?_ ⟨p, ⟨mem_univ _, hp⟩, hpx⟩ hx
      exact disjoint_left.mpr fun z hz hz' => ne_of_gt hz.2 hz'.2
    let t := max B 0 + 1
    have ht : 0 < t := by dsimp [t]; linarith [le_max_right B 0]
    have hmem : t ∈ Prod.snd '' (e.symm '' K') := by
      refine ⟨(p.1, t), ⟨e (p.1, t), ?_, e.symm_apply_apply _⟩, rfl⟩
      exact hsub ⟨(p.1, t), ⟨mem_univ _, ht⟩, rfl⟩
    have hbound := hB hmem
    dsimp [t] at hbound
    linarith [le_max_left B 0]

end PoincareConjecture.DeepHorn
