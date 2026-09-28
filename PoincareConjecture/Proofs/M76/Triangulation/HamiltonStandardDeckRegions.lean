import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence
import Mathlib.Topology.Connected.Clopen
import Mathlib.LinearAlgebra.Dual.Lemmas










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem disjoint_frontier_region_trichotomy [Nontrivial E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    (hUc : IsConnected U) (hVc : IsConnected V)
    (hUf : IsConnected (frontier U)) (hVf : IsConnected (frontier V))
    (hdis : Disjoint (frontier U) (frontier V)) :
    Disjoint (closure U) (closure V) ∨
      closure U ⊆ closure V ∨ closure V ⊆ closure U := by
  have hsideU := hUf.isPreconnected.subset_or_subset_compl_closure hV hdis.symm
  have hsideV := hVf.isPreconnected.subset_or_subset_compl_closure hU hdis
  have havoid {P Q : Set E} (h : frontier Q ⊆ (closure P)ᶜ) :
      Disjoint (frontier Q) P := by
    exact Set.disjoint_left.mpr fun x hxQ hxP => h hxQ (subset_closure hxP)
  rcases hsideU with hUin | hUout
  · rcases hsideV with hVin | hVout
    · have hfront : frontier (U ∪ V) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hnot : x ∉ U ∪ V := by
          simpa only [(hU.union hV).interior_eq] using hx.2
        have hcl : x ∈ closure U ∪ closure V := by
          rw [← closure_union]
          exact hx.1
        rcases hcl with hxU | hxV
        · exact hnot (Or.inr (hUin ⟨hxU,
            fun hi => hnot (Or.inl (interior_subset hi))⟩))
        · exact hnot (Or.inl (hVin ⟨hxV,
            fun hi => hnot (Or.inr (interior_subset hi))⟩))
      have hall := (isClopen_iff_frontier_eq_empty.mpr hfront).eq_univ
        (hUc.nonempty.mono subset_union_left)
      exact (NormedSpace.unbounded_univ ℝ E (hall ▸ hUb.union hVb)).elim
    · right
      left
      apply closure_mono
      apply hUc.isPreconnected.m76_subset_of_disjoint_frontier hV (havoid hVout)
      obtain ⟨x, hx⟩ := hUf.nonempty
      exact (closure_inter_open_nonempty_iff hV).mp
        ⟨x, frontier_subset_closure hx, hUin hx⟩
  · rcases hsideV with hVin | hVout
    · right
      right
      apply closure_mono
      apply hVc.isPreconnected.m76_subset_of_disjoint_frontier hU (havoid hUout)
      obtain ⟨x, hx⟩ := hVf.nonempty
      exact (closure_inter_open_nonempty_iff hU).mp
        ⟨x, frontier_subset_closure hx, hVin hx⟩
    · left
      have hopen : Disjoint U V := by
        apply Set.disjoint_left.mpr
        intro x hxU hxV
        have hsub := hUc.isPreconnected.m76_subset_of_disjoint_frontier hV
          (havoid hVout) ⟨x, hxU, hxV⟩
        obtain ⟨y, hy⟩ := hUf.nonempty
        exact hUout hy (closure_mono hsub (frontier_subset_closure hy))
      apply Set.disjoint_iff_inter_eq_empty.mpr
      rw [Set.closure_inter_eq_frontier_inter_of_disjoint_open hU hV hopen]
      exact Set.disjoint_iff_inter_eq_empty.mp hdis

private theorem compact_nonempty_not_contains_translate [FiniteDimensional ℝ E]
    {B : Set E} (hB : IsCompact B) (hne : B.Nonempty) {v : E} (hv : v ≠ 0) :
    ¬ (fun x => v + x) '' B ⊆ B := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℝ hv
  obtain ⟨x, hx, hmax⟩ := hB.exists_isMaxOn hne
    f.continuous_of_finiteDimensional.continuousOn
  intro hsub
  have hle := hmax (hsub ⟨x, hx, rfl⟩)
  change f (v + x) ≤ f x at hle
  rw [map_add, hf] at hle
  linarith

private theorem compact_nonempty_not_contained_in_translate [FiniteDimensional ℝ E]
    {B : Set E} (hB : IsCompact B) (hne : B.Nonempty) {v : E} (hv : v ≠ 0) :
    ¬ B ⊆ (fun x => v + x) '' B := by
  intro hsub
  apply compact_nonempty_not_contains_translate hB hne (neg_ne_zero.mpr hv)
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hsub hx
  rw [← hzx]
  simpa only [← add_assoc, neg_add_cancel, zero_add] using hz





theorem disjoint_closure_translate_of_disjoint_frontier [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUc : IsConnected U) (hUf : IsConnected (frontier U))
    {v : E} (hv : v ≠ 0)
    (hdis : Disjoint (frontier U) ((fun x => v + x) '' frontier U)) :
    Disjoint (closure U) ((fun x => v + x) '' closure U) := by
  let : Nontrivial E := ⟨⟨v, 0, hv⟩⟩
  let t : E ≃ₜ E := (ContinuousAffineEquiv.constVAdd ℝ E v).toHomeomorph
  let V : Set E := t '' U
  have hV : IsOpen V := t.isOpen_image.mpr hU
  have hB : IsCompact (closure U) := hUb.isCompact_closure
  have hVb : Bornology.IsBounded V :=
    (hB.image t.continuous).isBounded.subset (image_mono subset_closure)
  have hVc : IsConnected V := hUc.image t t.continuous.continuousOn
  have hVf : IsConnected (frontier V) := by
    rw [← t.image_frontier]
    exact hUf.image t t.continuous.continuousOn
  have hdis' : Disjoint (frontier U) (frontier V) := by
    rw [← t.image_frontier]
    exact hdis
  have hcl : closure V = (fun x => v + x) '' closure U :=
    (t.image_closure U).symm
  rcases disjoint_frontier_region_trichotomy hU hV hUb hVb hUc hVc hUf hVf hdis'
      with h | h | h
  · rwa [hcl] at h
  · exact (compact_nonempty_not_contained_in_translate hB
      (hUc.nonempty.mono subset_closure) hv (hcl ▸ h)).elim
  · exact (compact_nonempty_not_contains_translate hB
      (hUc.nonempty.mono subset_closure) hv (hcl ▸ h)).elim






theorem injOn_closure_of_injOn_connected_frontier [FiniteDimensional ℝ E]
    {A : Type*} [AddGroup A] (p : E →+ A)
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUc : IsConnected U) (hUf : IsConnected (frontier U))
    (hp : InjOn p (frontier U)) : InjOn p (closure U) := by
  intro x hx y hy hxy
  by_contra hne
  let v := x - y
  have hv : v ≠ 0 := sub_ne_zero.mpr hne
  have hpv : p v = 0 := by simp only [v, map_sub, hxy, sub_self]
  have hdis : Disjoint (frontier U) ((fun z => v + z) '' frontier U) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨w, hw, hwz⟩
    have hzw : z = w := hp hz hw (by rw [← hwz, map_add, hpv, zero_add])
    apply hv
    exact add_right_cancel (show v + w = 0 + w by simpa only [zero_add] using hwz.trans hzw)
  have hballs := disjoint_closure_translate_of_disjoint_frontier hU hUb hUc hUf hv hdis
  exact Set.disjoint_left.mp hballs hx ⟨y, hy, sub_add_cancel x y⟩

end PoincareConjecture.M76
