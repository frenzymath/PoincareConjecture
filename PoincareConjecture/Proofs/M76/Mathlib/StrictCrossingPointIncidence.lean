import PoincareConjecture.Proofs.M76.Mathlib.RegularEdgeCrossing

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem StraddlesZero.ne_zero {A : E →ᵃ[ℝ] ℝ} {e : Finset E}
    (he : A.StraddlesZero e) {v : E} (hv : v ∈ e) : A v ≠ 0 := by
  obtain ⟨u, w, hu, hw, heq⟩ := he
  have hv' : v ∈ ({u, w} : Set E) := heq ▸ hv
  rcases hv' with rfl | rfl
  · exact hu.ne
  · exact hw.ne'

end AffineMap

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem eq_edge_of_straddling_zero_point (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {e f : Finset E}
    (he : e ∈ K.faces) (hf : f ∈ K.faces) (hAe : A.StraddlesZero e)
    (hfcard : f.card = 2) {x : E}
    (hxe : x ∈ convexHull ℝ (e : Set E))
    (hxf : x ∈ convexHull ℝ (f : Set E)) (hAx : A x = 0) : e = f := by
  classical
  have hecard := AffineMap.StraddlesZero.card A hAe
  by_contra hne
  have hx : x ∈ convexHull ℝ ((e ∩ f : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull he hf]
    exact ⟨hxe, hxf⟩
  have hneinter : e ∩ f ≠ e := by
    intro hi
    exact hne (Finset.eq_of_subset_of_card_le
      (hi ▸ Finset.inter_subset_right) (by omega))
  have hlt := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hneinter⟩)
  have hpos := (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hx⟩)).card_pos
  have hcard : (e ∩ f).card = 1 := by omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  have hve : v ∈ e := Finset.inter_subset_left (by rw [hv]; exact Finset.mem_singleton_self v)
  rw [hv, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hx
  exact hAe.ne_zero hve (hx ▸ hAx)

theorem straddlingPoint_injective_without_regularity (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) :
    Function.Injective (fun e : {e : Finset E | e ∈ K.faces ∧ A.StraddlesZero e} =>
      A.straddlingPoint e.val e.property.2) := by
  intro e f hef
  change A.straddlingPoint e.val e.property.2 = A.straddlingPoint f.val f.property.2 at hef
  apply Subtype.ext
  have he := A.straddlingPoint_mem e.val e.property.2
  have hf := A.straddlingPoint_mem f.val f.property.2
  exact K.eq_edge_of_straddling_zero_point A e.property.1 f.property.1 e.property.2
    (AffineMap.StraddlesZero.card A f.property.2) he.1 (by rw [hef]; exact hf.1) he.2

theorem straddlingPoint_ne_vertex (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    {e : Finset E} (he : e ∈ K.faces) (hAe : A.StraddlesZero e)
    {q : E} (hq : q ∈ K.vertices) : A.straddlingPoint e hAe ≠ q := by
  intro hpq
  have hp := A.straddlingPoint_mem e hAe
  rw [hpq] at hp
  exact hAe.ne_zero ((K.vertex_mem_convexHull_iff hq he).mp hp.1) hp.2

end Geometry.SimplicialComplex
