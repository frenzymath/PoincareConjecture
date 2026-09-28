import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeLevel











set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]



theorem eq_edgeLevel_of_mem_affineSpan (A : E →ᵃ[ℝ] ℝ) {v u x : E} {c : ℝ}
    (hu : A u ≠ A v) (hx : x ∈ affineSpan ℝ ({v, u} : Set E)) (hAx : A x = c) :
    x = A.edgeLevel v u c := by
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  rw [apply_lineMap, lineMap_apply_ring'] at hAx
  have ht : t = (c - A v) / (A u - A v) := by
    apply (eq_div_iff (sub_ne_zero.mpr hu)).mpr
    linarith
  rw [edgeLevel_eq_lineMap, ht]



theorem edgeLevel_reverse (A : E →ᵃ[ℝ] ℝ) {v u : E} (hu : A u ≠ A v) (c : ℝ) :
    A.edgeLevel u v c = A.edgeLevel v u c := by
  apply A.eq_edgeLevel_of_mem_affineSpan hu
  · rw [edgeLevel_eq_lineMap, Set.pair_comm]
    exact lineMap_mem_affineSpan_pair _ u v
  · exact A.apply_edgeLevel hu.symm c



theorem edgeLevel_neg (A : E →ᵃ[ℝ] ℝ) {v u : E} (hu : A u ≠ A v) (c : ℝ) :
    (-A).edgeLevel v u (-c) = A.edgeLevel v u c := by
  apply A.eq_edgeLevel_of_mem_affineSpan hu
  · rw [edgeLevel_eq_lineMap]
    exact lineMap_mem_affineSpan_pair _ v u
  · have hneg : (-A) u ≠ (-A) v := fun h => hu (neg_injective h)
    have h := (-A).apply_edgeLevel hneg (-c)
    exact neg_injective h

end AffineMap
