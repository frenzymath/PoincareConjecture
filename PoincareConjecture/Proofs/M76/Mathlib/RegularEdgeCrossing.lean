import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroCrossing
import Mathlib.Analysis.Convex.SimplicialComplex.Basic










set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]



theorem StraddlesZero.card (A : E →ᵃ[ℝ] ℝ) {e : Finset E}
    (he : A.StraddlesZero e) : e.card = 2 := by
  classical
  obtain ⟨u, v, hu, hv, he⟩ := he
  have hefin : e = {u, v} := by
    apply Finset.coe_injective
    simpa only [Finset.coe_pair] using he
  rw [hefin]
  exact Finset.card_pair (fun h => by subst v; exact hu.not_gt hv)



noncomputable def straddlingPoint (A : E →ᵃ[ℝ] ℝ) (e : Finset E)
    (he : A.StraddlesZero e) : E :=
  (StraddlesZero.existsUnique A he).exists.choose



theorem straddlingPoint_mem (A : E →ᵃ[ℝ] ℝ) (e : Finset E)
    (he : A.StraddlesZero e) :
    A.straddlingPoint e he ∈ convexHull ℝ (e : Set E) ∧ A (A.straddlingPoint e he) = 0 :=
  (StraddlesZero.existsUnique A he).exists.choose_spec

end AffineMap

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]




theorem eq_edges_of_regular_zero_point (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0) {e f : Finset E}
    (he : e ∈ K.faces) (hf : f ∈ K.faces) (hecard : e.card = 2) (hfcard : f.card = 2)
    {x : E} (hxe : x ∈ convexHull ℝ (e : Set E))
    (hxf : x ∈ convexHull ℝ (f : Set E)) (hAx : A x = 0) : e = f := by
  classical
  by_contra hne
  have hx : x ∈ convexHull ℝ ((e ∩ f : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull he hf]
    exact ⟨hxe, hxf⟩
  have hneinter : e ∩ f ≠ e := by
    intro hi
    have hef : e ⊆ f := hi ▸ Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le hef (by omega))
  have hlt := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hneinter⟩)
  have hpos := (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hx⟩)).card_pos
  have hcard : (e ∩ f).card = 1 := by omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  have hve : v ∈ e := Finset.inter_subset_left (by rw [hv]; exact Finset.mem_singleton_self v)
  have hvK : v ∈ K.vertices := K.down_closed he (Finset.singleton_subset_iff.mpr hve)
    (Finset.singleton_nonempty v)
  rw [hv, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hx
  exact hreg v hvK (hx ▸ hAx)




theorem straddlingPoint_injective (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hreg : ∀ v ∈ K.vertices, A v ≠ 0) :
    Function.Injective (fun e : {e : Finset E | e ∈ K.faces ∧ A.StraddlesZero e} =>
      A.straddlingPoint e.val e.property.2) := by
  intro e f hef
  change A.straddlingPoint e.val e.property.2 = A.straddlingPoint f.val f.property.2 at hef
  apply Subtype.ext
  have he := A.straddlingPoint_mem e.val e.property.2
  have hf := A.straddlingPoint_mem f.val f.property.2
  apply K.eq_edges_of_regular_zero_point A hreg e.property.1 f.property.1
    (AffineMap.StraddlesZero.card A e.property.2) (AffineMap.StraddlesZero.card A f.property.2)
    he.1
  · rw [hef]
    exact hf.1
  · exact he.2

end Geometry.SimplicialComplex
