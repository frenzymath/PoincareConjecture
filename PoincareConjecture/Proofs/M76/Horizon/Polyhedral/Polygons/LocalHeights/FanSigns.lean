import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.Graph

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem straddlesZero_pair_iff (A : E →ᵃ[ℝ] ℝ) (u v : E) :
    A.StraddlesZero ({u, v} : Finset E) ↔
      (A u < 0 ∧ 0 < A v) ∨ (A v < 0 ∧ 0 < A u) := by
  constructor
  · rintro ⟨x, y, hx, hy, hpair⟩
    have hxm : x ∈ ({u, v} : Finset E) := by
      change x ∈ (↑({u, v} : Finset E) : Set E)
      rw [hpair]
      simp
    have hym : y ∈ ({u, v} : Finset E) := by
      change y ∈ (↑({u, v} : Finset E) : Set E)
      rw [hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxm hym
    rcases hxm with rfl | rfl <;> rcases hym with rfl | rfl
    · exact False.elim (hx.not_gt hy)
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
    · exact False.elim (hx.not_gt hy)
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact ⟨u, v, hu, hv, Finset.coe_pair⟩
    · exact ⟨v, u, hv, hu, by rw [Finset.coe_pair, Set.pair_comm]⟩

end AffineMap

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem existsUnique_triangleCrossingEdge_of_fan (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    {q a u v : E}
    (htu : ({q, a, u} : Finset E) ∈ K.faces) (htuc : ({q, a, u} : Finset E).card = 3)
    (htv : ({q, a, v} : Finset E) ∈ K.faces) (htvc : ({q, a, v} : Finset E).card = 3)
    (ha : A {q, a, u} a ≠ 0) (haa : A {q, a, u} a = A {q, a, v} a)
    (hu : A {q, a, u} u < 0) (hv : 0 < A {q, a, v} v) :
    ∃! e : K.triangleCrossingEdges A, e.val = {a, u} ∨ e.val = {a, v} := by
  have hesu : ({a, u} : Finset E) ⊆ {q, a, u} := Finset.subset_insert _ _
  have hesv : ({a, v} : Finset E) ⊆ {q, a, v} := Finset.subset_insert _ _
  have heKu : ({a, u} : Finset E) ∈ K.faces := K.down_closed htu hesu (by simp)
  have heKv : ({a, v} : Finset E) ∈ K.faces := K.down_closed htv hesv (by simp)
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hav : A {q, a, v} a < 0 := haa ▸ ha
    have hev : (A {q, a, v}).StraddlesZero ({a, v} : Finset E) :=
      ((A {q, a, v}).straddlesZero_pair_iff a v).mpr (Or.inl ⟨hav, hv⟩)
    let e : K.triangleCrossingEdges A := ⟨{a, v}, heKv, {q, a, v}, htv, htvc, hesv, hev⟩
    refine ⟨e, Or.inr rfl, ?_⟩
    intro f hf
    rcases hf with hf | hf
    · have hft : f.val ⊆ {q, a, u} := hf ▸ hesu
      have hstr := K.triangleCrossingEdge_straddles hA f htu htuc hft
      rw [hf, (A {q, a, u}).straddlesZero_pair_iff] at hstr
      rcases hstr with hstr | hstr <;> linarith
    · exact Subtype.ext hf
  · have hav : 0 < A {q, a, v} a := haa ▸ ha
    have heu : (A {q, a, u}).StraddlesZero ({a, u} : Finset E) :=
      ((A {q, a, u}).straddlesZero_pair_iff a u).mpr (Or.inr ⟨hu, ha⟩)
    let e : K.triangleCrossingEdges A := ⟨{a, u}, heKu, {q, a, u}, htu, htuc, hesu, heu⟩
    refine ⟨e, Or.inl rfl, ?_⟩
    intro f hf
    rcases hf with hf | hf
    · exact Subtype.ext hf
    · have hft : f.val ⊆ {q, a, v} := hf ▸ hesv
      have hstr := K.triangleCrossingEdge_straddles hA f htv htvc hft
      rw [hf, (A {q, a, v}).straddlesZero_pair_iff] at hstr
      rcases hstr with hstr | hstr <;> linarith

end Geometry.SimplicialComplex
