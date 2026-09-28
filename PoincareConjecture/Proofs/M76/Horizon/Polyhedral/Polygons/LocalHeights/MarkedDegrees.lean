import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.FanSigns
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem triangleSliceGraph_marked_neighbor_pair (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    {q a b u v : E} (hq : q ∈ K.triangleZeroVertices A)
    (hau : ({q, a, u} : Finset E) ∈ K.faces) (hauc : ({q, a, u} : Finset E).card = 3)
    (hav : ({q, a, v} : Finset E) ∈ K.faces) (havc : ({q, a, v} : Finset E).card = 3)
    (hbu : ({q, b, u} : Finset E) ∈ K.faces) (hbuc : ({q, b, u} : Finset E).card = 3)
    (hbv : ({q, b, v} : Finset E) ∈ K.faces) (hbvc : ({q, b, v} : Finset E).card = 3)
    (htriangles : ∀ t ∈ K.faces, t.card = 3 → q ∈ t →
      t = {q, a, u} ∨ t = {q, a, v} ∨ t = {q, b, u} ∨ t = {q, b, v})
    (hab : a ≠ b)
    (ha : A {q, a, u} a ≠ 0) (haa : A {q, a, u} a = A {q, a, v} a)
    (hb : A {q, b, u} b ≠ 0) (hbb : A {q, b, u} b = A {q, b, v} b)
    (hua : A {q, a, u} u < 0) (hva : 0 < A {q, a, v} v)
    (hub : A {q, b, u} u < 0) (hvb : 0 < A {q, b, v} v) :
    ∃ e f : K.triangleCrossingEdges A, e ≠ f ∧
      ∀ w : K.TriangleSliceLabel A,
        (K.triangleSliceGraph A).Adj (.inl ⟨q, hq⟩) w ↔ w = .inr e ∨ w = .inr f := by
  obtain ⟨e, hec, heunique⟩ :=
    K.existsUnique_triangleCrossingEdge_of_fan hA hau hauc hav havc ha haa hua hva
  obtain ⟨f, hfc, hfunique⟩ :=
    K.existsUnique_triangleCrossingEdge_of_fan hA hbu hbuc hbv hbvc hb hbb hub hvb
  have hqau : A {q, a, u} q = 0 := K.triangleZeroVertex_zero hA ⟨q, hq⟩ hau hauc (by simp)
  have hqav : A {q, a, v} q = 0 := K.triangleZeroVertex_zero hA ⟨q, hq⟩ hav havc (by simp)
  have hqbu : A {q, b, u} q = 0 := K.triangleZeroVertex_zero hA ⟨q, hq⟩ hbu hbuc (by simp)
  have hqa : q ≠ a := fun h => ha (h ▸ hqau)
  have hqb : q ≠ b := fun h => hb (h ▸ hqbu)
  have hqu : q ≠ u := fun h => hua.ne (h ▸ hqau)
  have hqv : q ≠ v := fun h => hva.ne' (h ▸ hqav)
  have hau' : a ≠ u := by intro h; simp [h, hqu] at hauc
  have hav' : a ≠ v := by intro h; simp [h, hqv] at havc
  have hef : e ≠ f := by
    intro h
    have ham : a ∈ e.val := by rcases hec with hec | hec <;> rw [hec] <;> simp
    rw [h] at ham
    rcases hfc with hfc | hfc <;> rw [hfc] at ham
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ham
      exact ham.elim hab hau'
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ham
      exact ham.elim hab hav'
  have hadje : (K.triangleSliceGraph A).Adj (.inl ⟨q, hq⟩) (.inr e) := by
    change {q} ∪ e.val ∈ K.faces ∧ ({q} ∪ e.val).card = 3
    rw [Finset.singleton_union]
    rcases hec with hec | hec
    · rw [hec]; exact ⟨hau, hauc⟩
    · rw [hec]; exact ⟨hav, havc⟩
  have hadjf : (K.triangleSliceGraph A).Adj (.inl ⟨q, hq⟩) (.inr f) := by
    change {q} ∪ f.val ∈ K.faces ∧ ({q} ∪ f.val).card = 3
    rw [Finset.singleton_union]
    rcases hfc with hfc | hfc
    · rw [hfc]; exact ⟨hbu, hbuc⟩
    · rw [hfc]; exact ⟨hbv, hbvc⟩
  refine ⟨e, f, hef, ?_⟩
  intro w
  constructor
  · intro hw
    cases w with
    | inl r => exact False.elim (K.triangleSliceGraph_not_adj_zero A ⟨q, hq⟩ r hw)
    | inr d =>
      change {q} ∪ d.val ∈ K.faces ∧ ({q} ∪ d.val).card = 3 at hw
      rw [Finset.singleton_union] at hw
      have hzero := K.triangleZeroVertex_zero hA ⟨q, hq⟩ hw.1 hw.2 (by simp)
      have hstr := K.triangleCrossingEdge_straddles hA d hw.1 hw.2 (Finset.subset_insert _ _)
      have hqd : q ∉ d.val := fun h => hstr.ne_zero h hzero
      have hclasses := htriangles (insert q d.val) hw.1 hw.2 (by simp)
      have herase : ∀ x y : E, q ≠ x → q ≠ y →
          insert q d.val = {q, x, y} → d.val = {x, y} := by
        intro x y hqx hqy h
        have hh := congrArg (fun s : Finset E => s.erase q) h
        simpa [hqd, hqx, hqy] using hh
      rcases hclasses with h | h | h | h
      · exact Or.inl (congrArg Sum.inr (heunique d (Or.inl (herase a u hqa hqu h))))
      · exact Or.inl (congrArg Sum.inr (heunique d (Or.inr (herase a v hqa hqv h))))
      · exact Or.inr (congrArg Sum.inr (hfunique d (Or.inl (herase b u hqb hqu h))))
      · exact Or.inr (congrArg Sum.inr (hfunique d (Or.inr (herase b v hqb hqv h))))
  · rintro (rfl | rfl)
    · exact hadje
    · exact hadjf

end Geometry.SimplicialComplex
