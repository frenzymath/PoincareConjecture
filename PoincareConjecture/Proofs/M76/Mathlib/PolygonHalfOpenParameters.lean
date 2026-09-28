import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalEdges










set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in



theorem edge_endpoints_ne_of_injective (P : Polygon E (n + 3))
    (hinj : Function.Injective P) (i : Fin (n + 3)) :
    P i ≠ P (finRotate (n + 3) i) := by
  intro h
  have hi := (hinj h).symm
  rw [finRotate_apply] at hi
  have h1 : (1 : Fin (n + 3)) = 0 := add_left_cancel
    (show i + 1 = i + 0 by simpa only [add_zero] using hi)
  have hv := congrArg Fin.val h1
  norm_num at hv





theorem eq_of_halfOpen_edge_parameters (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {i j : Fin (n + 3)} {a b : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1)
    (he : AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) a =
      AffineMap.lineMap (P j) (P (finRotate (n + 3) j)) b) : i = j ∧ a = b := by
  let x := AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) a
  have hxi : x ∈ P.edgeSet ℝ i := ⟨a, ⟨ha.1, ha.2.le⟩, rfl⟩
  have hxj : x ∈ P.edgeSet ℝ j := ⟨b, ⟨hb.1, hb.2.le⟩, he.symm⟩
  have hfirst (k l : Fin (n + 3)) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1)
      (hkt : P k = AffineMap.lineMap (P l) (P (finRotate (n + 3) l)) t) : k = l := by
    have hkl := (P.vertex_mem_edgeSet_iff hP hinj k l).mp
      (show P k ∈ P.edgeSet ℝ l from ⟨t, ⟨ht.1, ht.2.le⟩, hkt.symm⟩)
    apply hkl.resolve_right
    intro hk
    have ht1 : t = 1 := AffineMap.lineMap_injective ℝ (P.edge_endpoints_ne_of_injective hinj l)
      (by rw [AffineMap.lineMap_apply_one]; exact hkt.symm.trans (congrArg P hk))
    exact ht.2.ne ht1
  have hij : i = j := by
    by_cases hxv : x ∈ range P
    · obtain ⟨k, hk⟩ := hxv
      exact (hfirst k i a ha hk).symm.trans (hfirst k j b hb (hk.trans he))
    · exact P.eq_of_mem_edgeSets_of_not_vertex hP hinj hxv hxi hxj
  subst j
  exact ⟨rfl, AffineMap.lineMap_injective ℝ (P.edge_endpoints_ne_of_injective hinj i) he⟩

end Polygon
