import PoincareConjecture.Proofs.M76.Mathlib.TriangleZeroSlice









set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]



theorem straddlesZero_of_regular_zero (A : E →ᵃ[ℝ] ℝ) {e : Finset E}
    (he : e.card = 2) (hreg : ∀ u ∈ e, A u ≠ 0) {x : E}
    (hx : x ∈ convexHull ℝ (e : Set E)) (hAx : A x = 0) : A.StraddlesZero e := by
  classical
  obtain ⟨u, hu, v, hv, hAu, hAv⟩ := A.exists_opposite_vertices_of_regular_zero hreg hx hAx
  have huv : u ≠ v := fun h => (h ▸ hAu).not_gt hAv
  have hsub : ({u, v} : Finset E) ⊆ e :=
    Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [he, Finset.card_pair huv])
  exact ⟨u, v, hAu, hAv, by rw [← heq, Finset.coe_pair]⟩




theorem segment_straddlingPoints_eq_triangleSlice (A : E →ᵃ[ℝ] ℝ)
    {e f t : Finset E} (he : A.StraddlesZero e) (hf : A.StraddlesZero f)
    (ht : t.card = 3) (hreg : ∀ u ∈ t, A u ≠ 0)
    (het : e ⊆ t) (hft : f ⊆ t) (hne : e ≠ f) :
    segment ℝ (A.straddlingPoint e he) (A.straddlingPoint f hf) =
      convexHull ℝ (t : Set E) ∩ {x | A x = 0} := by
  classical
  have hpoint := A.straddlingPoint_mem e he
  obtain ⟨e', f', he', hf', he't, hf't, hne', hslice⟩ :=
    A.exists_straddling_edges_triangle ht hreg
      ⟨A.straddlingPoint e he, convexHull_mono het hpoint.1, hpoint.2⟩
  have hcolor {g : Finset E} (hg : A.StraddlesZero g) (hgt : g ⊆ t) :
      g.IsBichromaticPair (fun u => decide (0 < A u)) :=
    (A.straddlesZero_iff_bichromatic g (fun u hu => hreg u (hgt hu))).mp hg
  have hchoices {g : Finset E} (hg : A.StraddlesZero g) (hgt : g ⊆ t) : g = e ∨ g = f :=
    (hcolor he het).eq_or_eq_of_subset_triangle (hcolor hf hft) (hcolor hg hgt)
      ht het hft hgt hne
  rcases hchoices he' he't with rfl | rfl <;>
    rcases hchoices hf' hf't with rfl | rfl
  · exact (hne' rfl).elim
  · exact hslice.symm
  · exact (segment_symm ℝ _ _).trans hslice.symm
  · exact (hne' rfl).elim

end AffineMap

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]




theorem common_straddling_edge_of_triangle_intersection
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0) {t u : Finset E}
    (ht : t ∈ K.faces) (hu : u ∈ K.faces) (htcard : t.card = 3) (hucard : u.card = 3)
    (hne : t ≠ u) {x : E} (hxt : x ∈ convexHull ℝ (t : Set E))
    (hxu : x ∈ convexHull ℝ (u : Set E)) (hAx : A x = 0) :
    ∃ (e : Finset E) (he : A.StraddlesZero e), e ∈ K.faces ∧ e ⊆ t ∧ e ⊆ u ∧
      A.straddlingPoint e he = x := by
  classical
  have hx : x ∈ convexHull ℝ ((t ∩ u : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull ht hu]
    exact ⟨hxt, hxu⟩
  have hvreg : ∀ v ∈ t ∩ u, A v ≠ 0 := by
    intro v hv
    exact hreg v (K.down_closed ht
      (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp hv).1) (Finset.singleton_nonempty v))
  obtain ⟨a, ha, b, hb, hAa, hAb⟩ := A.exists_opposite_vertices_of_regular_zero hvreg hx hAx
  have hab : a ≠ b := fun h => (h ▸ hAa).not_gt hAb
  have hsub : ({a, b} : Finset E) ⊆ t ∩ u :=
    Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
  have hlo := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at hlo
  have hneinter : t ∩ u ≠ t := fun heq => hne
    (Finset.eq_of_subset_of_card_le (heq ▸ Finset.inter_subset_right) (by omega))
  have hhi := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hneinter⟩)
  have hcard : (t ∩ u).card = 2 := by omega
  have he := A.straddlesZero_of_regular_zero hcard hvreg hx hAx
  refine ⟨t ∩ u, he, K.down_closed ht Finset.inter_subset_left
    (Finset.card_pos.mp (by omega)), Finset.inter_subset_left, Finset.inter_subset_right, ?_⟩
  exact (AffineMap.StraddlesZero.existsUnique A he).unique
    (A.straddlingPoint_mem _ he) ⟨hx, hAx⟩

end Geometry.SimplicialComplex
