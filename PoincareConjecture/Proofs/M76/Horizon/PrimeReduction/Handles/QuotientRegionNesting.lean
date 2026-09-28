import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem disjoint_or_nested_closures_of_disjoint_connected_frontiers
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V)
    (hUf : IsConnected (frontier U)) (hVf : IsConnected (frontier V))
    (hdis : Disjoint (frontier U) (frontier V)) (hproper : U ∪ V ≠ univ) :
    Disjoint (closure U) (closure V) ∨ closure U ⊆ closure V ∨ closure V ⊆ closure U := by
  have hsideU := hUf.isPreconnected.subset_or_subset_compl_closure hV hdis.symm
  have hsideV := hVf.isPreconnected.subset_or_subset_compl_closure hU hdis
  have havoid {P Q : Set X} (h : frontier Q ⊆ (closure P)ᶜ) :
      Disjoint (frontier Q) P :=
    disjoint_left.mpr fun x hxQ hxP => h hxQ (subset_closure hxP)
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
      exact (hproper ((isClopen_iff_frontier_eq_empty.mpr hfront).eq_univ
        (hUc.nonempty.mono subset_union_left))).elim
    · right
      left
      apply closure_mono
      apply hUc.isPreconnected.m76_subset_of_disjoint_frontier hV (havoid hVout)
      obtain ⟨x,hx⟩ := hUf.nonempty
      exact (closure_inter_open_nonempty_iff hV).mp
        ⟨x,frontier_subset_closure hx,hUin hx⟩
  · rcases hsideV with hVin | hVout
    · right
      right
      apply closure_mono
      apply hVc.isPreconnected.m76_subset_of_disjoint_frontier hU (havoid hUout)
      obtain ⟨x,hx⟩ := hVf.nonempty
      exact (closure_inter_open_nonempty_iff hU).mp
        ⟨x,frontier_subset_closure hx,hVin hx⟩
    · left
      have hopen : Disjoint U V := by
        apply disjoint_left.mpr
        intro x hxU hxV
        have hsub := hUc.isPreconnected.m76_subset_of_disjoint_frontier hV
          (havoid hVout) ⟨x,hxU,hxV⟩
        obtain ⟨y,hy⟩ := hUf.nonempty
        exact hUout hy (closure_mono hsub (frontier_subset_closure hy))
      apply disjoint_iff_inter_eq_empty.mpr
      rw [Set.closure_inter_eq_frontier_inter_of_disjoint_open hU hV hopen]
      exact disjoint_iff_inter_eq_empty.mp hdis

theorem disjoint_or_nested_projected_bounded_regions
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [AddGroup A]
    (p : E →+ A) {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    (hUc : IsConnected U) (hVc : IsConnected V)
    (hUf : IsConnected (frontier U)) (hVf : IsConnected (frontier V))
    (hdis : Disjoint (p '' frontier U) (p '' frontier V)) :
    Disjoint (p '' closure U) (p '' closure V) ∨
      p '' closure U ⊆ p '' closure V ∨ p '' closure V ⊆ p '' closure U := by
  classical
  by_cases hd : Disjoint (p '' closure U) (p '' closure V)
  · exact Or.inl hd
  obtain ⟨z,⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩ := not_disjoint_iff.mp hd
  let v := x - y
  have hpv : p v = 0 := by simp only [v,map_sub,hxz,hyz,sub_self]
  let t : E ≃ₜ E := (ContinuousAffineEquiv.constVAdd ℝ E v).toHomeomorph
  have hpt (w : E) : p (t w) = p w := by
    change p (v + w) = p w
    rw [map_add,hpv,zero_add]
  have hptImage (Z : Set E) : p '' (t '' Z) = p '' Z := by
    rw [image_image]
    exact image_congr fun w _ => hpt w
  have hVopen : IsOpen (t '' V) := t.isOpen_image.mpr hV
  have hVbound : Bornology.IsBounded (t '' V) :=
    (hVb.isCompact_closure.image t.continuous).isBounded.subset (image_mono subset_closure)
  have hVconn : IsConnected (t '' V) := hVc.image t t.continuous.continuousOn
  have hVfront : IsConnected (frontier (t '' V)) := by
    rw [← t.image_frontier]
    exact hVf.image t t.continuous.continuousOn
  have hfrontDis : Disjoint (frontier U) (frontier (t '' V)) := by
    rw [← t.image_frontier]
    apply disjoint_left.mpr
    rintro w hw ⟨w',hw',heq⟩
    apply disjoint_left.mp hdis (mem_image_of_mem p hw)
    exact ⟨w',hw',(hpt w').symm.trans (congrArg p heq)⟩
  have hproper : U ∪ t '' V ≠ univ := by
    intro heq
    exact NormedSpace.unbounded_univ ℝ E (heq ▸ hUb.union hVbound)
  have hcl : closure (t '' V) = t '' closure V := (t.image_closure V).symm
  rcases disjoint_or_nested_closures_of_disjoint_connected_frontiers
    hU hVopen hUc hVconn hUf hVfront hfrontDis hproper with h | h | h
  · have hxt : x ∈ closure (t '' V) := by
      rw [hcl]
      exact ⟨y,hy,sub_add_cancel x y⟩
    exact (disjoint_left.mp h hx hxt).elim
  · right
    left
    have h' := image_mono (f := p) h
    rwa [hcl,hptImage] at h'
  · right
    right
    have h' := image_mono (f := p) h
    rwa [hcl,hptImage] at h'

end PoincareConjecture.M76
