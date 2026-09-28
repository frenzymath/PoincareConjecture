import PoincareConjecture.Proofs.M76.Mathlib.UniformPolygonSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.PolygonHalfOpenParameters

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n m : ℕ}

theorem injective_subdivide (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (m + 2) → ℝ) (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last (m + 1)) = 1) :
    Function.Injective (P.subdivide t) := by
  have hparam (j : Fin (m + 1)) : t j.castSucc ∈ Ico (0 : ℝ) 1 := by
    constructor
    · rw [← ht0]
      exact ht.monotone (Fin.zero_le _)
    · rw [← ht1]
      apply ht
      change j.val < m + 1
      exact j.isLt
  intro k l he
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective l
  rw [P.subdivide_apply, P.subdivide_apply] at he
  obtain ⟨hi, hj⟩ := P.eq_of_halfOpen_edge_parameters hP hinj (hparam j) (hparam j') he
  exact congrArg finProdFinEquiv (Prod.ext hi (Fin.castSucc_injective (m + 1) (ht.injective hj)))

theorem hasSimplicialEdges_subdivide (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (m + 2) → ℝ) (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last (m + 1)) = 1) :
    (P.subdivide t).HasSimplicialEdges := by
  have hparam (j : Fin (m + 2)) : t j ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← ht0]
      exact ht.monotone (Fin.zero_le _)
    · rw [← ht1]
      exact ht.monotone (Fin.le_last _)
  have hend (i : Fin (n + 3)) (j : Fin (m + 1)) (r : ℝ) :
      AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) r ∈
        ((P.subdivide t).edgeVertices (finProdFinEquiv (i, j)) : Set E) ↔
      r = t j.castSucc ∨ r = t j.succ := by
    simp only [edgeVertices, Finset.coe_pair, mem_insert_iff, mem_singleton_iff,
      P.subdivide_apply, P.subdivide_rotate_apply t ht0 ht1,
      (AffineMap.lineMap_injective ℝ (P.edge_endpoints_ne_of_injective hinj i)).eq_iff]
  have hold (i : Fin (n + 3)) (j : Fin (m + 1)) {r : ℝ}
      (hr : r ∈ Icc (t j.castSucc) (t j.succ)) : r ∈ Icc (0 : ℝ) 1 :=
    ⟨(hparam _).1.trans hr.1, hr.2.trans (hparam _).2⟩
  have hvertex (i : Fin (n + 3)) (j : Fin (m + 1)) {r : ℝ}
      (hr : r ∈ Icc (t j.castSucc) (t j.succ))
      (hv : AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) r ∈ range P) :
      r = t j.castSucc ∨ r = t j.succ := by
    obtain ⟨v, hv⟩ := hv
    have hvend := (P.vertex_mem_edgeSet_iff hP hinj v i).mp
      (show P v ∈ P.edgeSet ℝ i from ⟨r, hold i j hr, hv.symm⟩)
    rcases hvend with hvend | hvend
    · have hr0 : r = 0 := AffineMap.lineMap_injective ℝ (P.edge_endpoints_ne_of_injective hinj i)
        (by rw [AffineMap.lineMap_apply_zero]; exact hv.symm.trans (congrArg P hvend))
      exact Or.inl (le_antisymm (by linarith [(hparam j.castSucc).1]) hr.1)
    · have hr1 : r = 1 := AffineMap.lineMap_injective ℝ (P.edge_endpoints_ne_of_injective hinj i)
        (by rw [AffineMap.lineMap_apply_one]; exact hv.symm.trans (congrArg P hvend))
      exact Or.inr (le_antisymm hr.2 (by linarith [(hparam j.succ).2]))
  intro k l x hx
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective l
  by_cases hi : i = i'
  · subst i'
    by_cases hj : j = j'
    · subst j'
      rw [inter_self, ← edgeSet_eq_convexHull]
      exact hx.1
    · obtain ⟨r, hr, hrx⟩ := (P.subdivide_edgeSet t ht ht0 ht1 i j) ▸ hx.1
      obtain ⟨s, hs, hsx⟩ := (P.subdivide_edgeSet t ht ht0 ht1 i j') ▸ hx.2
      have hrs : r = s := AffineMap.lineMap_injective ℝ
        (P.edge_endpoints_ne_of_injective hinj i) (hrx.trans hsx.symm)
      subst s
      obtain ⟨hjr, hjr'⟩ := ht.eq_endpoints_of_mem_consecutive_Icc hj hr hs
      apply subset_convexHull ℝ _
      exact hrx ▸ ⟨(hend i j r).mpr hjr, (hend i j' r).mpr hjr'⟩
  · obtain ⟨r, hr, hrx⟩ := (P.subdivide_edgeSet t ht ht0 ht1 i j) ▸ hx.1
    obtain ⟨s, hs, hsx⟩ := (P.subdivide_edgeSet t ht ht0 ht1 i' j') ▸ hx.2
    have hxi : x ∈ P.edgeSet ℝ i := ⟨r, hold i j hr, hrx⟩
    have hxi' : x ∈ P.edgeSet ℝ i' := ⟨s, hold i' j' hs, hsx⟩
    have hxv : x ∈ range P := by
      by_contra h
      exact hi (P.eq_of_mem_edgeSets_of_not_vertex hP hinj h hxi hxi')
    apply subset_convexHull ℝ _
    exact ⟨hrx ▸ (hend i j r).mpr (hvertex i j hr (hrx.symm ▸ hxv)),
      hsx ▸ (hend i' j' s).mpr (hvertex i' j' hs (hsx.symm ▸ hxv))⟩

end Polygon
