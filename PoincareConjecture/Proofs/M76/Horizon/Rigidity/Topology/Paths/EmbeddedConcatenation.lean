import Mathlib.Topology.Path
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set unitInterval

namespace Path

theorem injective_trans_of_range_inter_subset
    {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : range p ∩ range q ⊆ {b}) :
    Function.Injective (p.trans q) := by
  intro s t hst
  rw [trans_apply, trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have h := congrArg Subtype.val (hp hst)
    apply Subtype.ext
    dsimp at h
    linarith
  · have hb : p ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ = b :=
      hmeet ⟨⟨_, rfl⟩, ⟨_, hst.symm⟩⟩
    have h := congrArg Subtype.val (hq (hst.symm.trans (hb.trans q.source.symm)))
    dsimp at h
    exfalso
    linarith
  · have hb : q ⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩ = b :=
      hmeet ⟨⟨_, hst.symm⟩, ⟨_, rfl⟩⟩
    have h := congrArg Subtype.val (hq (hb.trans q.source.symm))
    dsimp at h
    exfalso
    linarith
  · have h := congrArg Subtype.val (hq hst)
    apply Subtype.ext
    dsimp at h
    linarith

theorem isEmbedding_trans_of_range_inter_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] {a b c : X}
    (p : Path a b) (q : Path b c)
    (hp : Topology.IsEmbedding p) (hq : Topology.IsEmbedding q)
    (hmeet : range p ∩ range q ⊆ {b}) :
    Topology.IsEmbedding (p.trans q) :=
  ((p.trans q).continuous.isClosedEmbedding
    (p.injective_trans_of_range_inter_subset q hp.injective hq.injective hmeet)).isEmbedding

theorem isEmbedding_trans_trans_of_range_inter_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] {a b c d : X}
    (p : Path a b) (q : Path b c) (r : Path c d)
    (hp : Topology.IsEmbedding p) (hq : Topology.IsEmbedding q)
    (hr : Topology.IsEmbedding r)
    (hpq : range p ∩ range q ⊆ {b})
    (hqr : range q ∩ range r ⊆ {c}) (hpr : Disjoint (range p) (range r)) :
    Topology.IsEmbedding ((p.trans q).trans r) := by
  apply (p.trans q).isEmbedding_trans_of_range_inter_subset r
    (p.isEmbedding_trans_of_range_inter_subset q hp hq hpq) hr
  rintro x ⟨hx, hxr⟩
  rw [trans_range] at hx
  rcases hx with hxp | hxq
  · exact False.elim (Set.disjoint_left.mp hpr hxp hxr)
  · exact hqr ⟨hxq, hxr⟩

theorem range_inter_subset_endpoint_of_frontier
    {X : Type*} [TopologicalSpace X] {R : Set X} {a b c : X}
    (p : Path a b) (q : Path b c)
    (hp : range p ⊆ frontier R)
    (hq : ∀ t, q t ∈ frontier R → t = 0 ∨ t = 1)
    (hc : c ∉ range p) : range p ∩ range q ⊆ {b} := by
  rintro x ⟨hxp, t, rfl⟩
  rcases hq t (hp hxp) with ht | ht
  · simp [ht]
  · exact False.elim (hc (by simpa [ht] using hxp))

end Path
