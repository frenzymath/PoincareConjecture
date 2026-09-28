import PoincareConjecture.Proofs.M76.Mathlib.PolygonInteriorCutArcs










set_option autoImplicit false

open Set AffineMap

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}



theorem cutArc_endpoints_subset (P : Polygon E n) (t : Fin n → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    {P.edgeCut t i, P.edgeCut t (finRotate n i)} ⊆ P.cutArc t i := by
  rintro x (rfl | rfl)
  · exact Or.inl ⟨t i, ⟨le_rfl, (ht i).2⟩, rfl⟩
  · exact Or.inr ⟨t (finRotate n i), ⟨(ht _).1, le_rfl⟩, rfl⟩





theorem vertex_mem_cutArc_iff (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (k i : Fin (n + 3)) :
    P k ∈ P.cutArc t i ↔ k = finRotate (n + 3) i := by
  constructor
  · rintro (⟨r, hr, he⟩ | ⟨r, hr, he⟩)
    · have hk := (P.vertex_mem_edgeSet_iff hP hinj k i).mp
        ⟨r, ⟨(ht i).1.le.trans hr.1, hr.2⟩, he⟩
      rcases hk with hk | hk
      · have he0 : lineMap (P i) (P (finRotate (n + 3) i)) r =
            lineMap (P i) (P (finRotate (n + 3) i)) (0 : ℝ) := by
          rw [lineMap_apply_zero]
          exact he.trans (congrArg P hk)
        have hr0 := lineMap_injective ℝ (P.edge_endpoints_ne_of_injective hinj i) he0
        exact False.elim ((not_le_of_gt (ht i).1) (hr0 ▸ hr.1))
      · exact hk
    · have hk := (P.vertex_mem_edgeSet_iff hP hinj k (finRotate (n + 3) i)).mp
        ⟨r, ⟨hr.1, hr.2.trans (ht _).2.le⟩, he⟩
      rcases hk with hk | hk
      · exact hk
      · have he1 : lineMap (P (finRotate (n + 3) i))
            (P (finRotate (n + 3) (finRotate (n + 3) i))) r =
              lineMap (P (finRotate (n + 3) i))
                (P (finRotate (n + 3) (finRotate (n + 3) i))) (1 : ℝ) := by
          rw [lineMap_apply_one]
          exact he.trans (congrArg P hk)
        have hr1 := lineMap_injective ℝ
          (P.edge_endpoints_ne_of_injective hinj (finRotate (n + 3) i)) he1
        exact False.elim ((not_le_of_gt (ht _).2) (hr1 ▸ hr.2))
  · rintro rfl
    exact Or.inl ⟨1, ⟨(ht i).2.le, le_rfl⟩, lineMap_apply_one _ _⟩





theorem cutArc_inter_of_ne (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    {i j : Fin (n + 3)} (hij : i ≠ j) :
    P.cutArc t i ∩ P.cutArc t j =
      ({P.edgeCut t i, P.edgeCut t (finRotate (n + 3) i)} ∩
        {P.edgeCut t j, P.edgeCut t (finRotate (n + 3) j)}) := by
  have htc (k) : t k ∈ Icc (0 : ℝ) 1 := ⟨(ht k).1.le, (ht k).2.le⟩
  apply Subset.antisymm
  · rintro x ⟨hxi, hxj⟩
    have hxv : x ∉ range P := by
      rintro ⟨k, rfl⟩
      have hi := (P.vertex_mem_cutArc_iff hP hinj t ht k i).mp hxi
      have hj := (P.vertex_mem_cutArc_iff hP hinj t ht k j).mp hxj
      exact hij ((finRotate (n + 3)).injective (hi.symm.trans hj))
    rcases hxi with ⟨u, hu, hux⟩ | ⟨u, hu, hux⟩ <;>
      rcases hxj with ⟨v, hv, hvx⟩ | ⟨v, hv, hvx⟩
    · exact False.elim (hij (P.eq_of_mem_edgeSets_of_not_vertex hP hinj hxv
        ⟨u, ⟨(ht i).1.le.trans hu.1, hu.2⟩, hux⟩
        ⟨v, ⟨(ht j).1.le.trans hv.1, hv.2⟩, hvx⟩))
    · have hi : i = finRotate (n + 3) j :=
        P.eq_of_mem_edgeSets_of_not_vertex hP hinj hxv
          ⟨u, ⟨(ht i).1.le.trans hu.1, hu.2⟩, hux⟩
          ⟨v, ⟨hv.1, hv.2.trans (ht _).2.le⟩, hvx⟩
      subst i
      have huv := lineMap_injective ℝ
        (P.edge_endpoints_ne_of_injective hinj (finRotate (n + 3) j))
        (hux.trans hvx.symm)
      have hut : u = t (finRotate (n + 3) j) :=
        le_antisymm (huv.symm ▸ hv.2) hu.1
      have hxcut : x = P.edgeCut t (finRotate (n + 3) j) :=
        hux.symm.trans (congrArg _ hut)
      exact ⟨Or.inl hxcut, Or.inr hxcut⟩
    · have hj : finRotate (n + 3) i = j :=
        P.eq_of_mem_edgeSets_of_not_vertex hP hinj hxv
          ⟨u, ⟨hu.1, hu.2.trans (ht _).2.le⟩, hux⟩
          ⟨v, ⟨(ht j).1.le.trans hv.1, hv.2⟩, hvx⟩
      subst j
      have huv := lineMap_injective ℝ
        (P.edge_endpoints_ne_of_injective hinj (finRotate (n + 3) i))
        (hux.trans hvx.symm)
      have hut : u = t (finRotate (n + 3) i) :=
        le_antisymm hu.2 (huv.symm ▸ hv.1)
      have hxcut : x = P.edgeCut t (finRotate (n + 3) i) :=
        hux.symm.trans (congrArg _ hut)
      exact ⟨Or.inr hxcut, Or.inl hxcut⟩
    · have heq := P.eq_of_mem_edgeSets_of_not_vertex hP hinj hxv
        ⟨u, ⟨hu.1, hu.2.trans (ht _).2.le⟩, hux⟩
        ⟨v, ⟨hv.1, hv.2.trans (ht _).2.le⟩, hvx⟩
      exact False.elim (hij ((finRotate (n + 3)).injective heq))
  · exact inter_subset_inter (P.cutArc_endpoints_subset t htc i)
      (P.cutArc_endpoints_subset t htc j)

end Polygon
