import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.DerivedSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.CentroidMesh

set_option autoImplicit false

open Set
open scoped BigOperators

namespace AffineIndependent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_positive_weights_of_mem_intrinsicInterior
    {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E))
    {p : E} (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    ∃ w : E → ℝ, (∀ v ∈ s, 0 < w v) ∧
      (∑ v ∈ s, w v) = 1 ∧ (∑ v ∈ s, w v • v) = p := by
  classical
  obtain ⟨w, hw, hsum, hval⟩ := Finset.mem_convexHull'.mp (intrinsicInterior_subset hp)
  refine ⟨w, ?_, hsum, hval⟩
  intro v hv
  by_contra hpos
  have hzero : w v = 0 := le_antisymm (not_lt.mp hpos) (hw v hv)
  have hperase : p ∈ convexHull ℝ ((s.erase v : Finset E) : Set E) := by
    apply Finset.mem_convexHull'.mpr
    refine ⟨w, fun x hx => hw x (Finset.mem_of_mem_erase hx), ?_, ?_⟩
    · exact (s.sum_erase hzero).trans hsum
    · exact (s.sum_erase (f := fun x => w x • x)
        (show w v • v = 0 by rw [hzero, zero_smul])).trans hval
  have hfront := hs.convexHull_subset_intrinsicFrontier (Finset.erase_ssubset hv) hperase
  rw [← intrinsicClosure_sdiff_intrinsicInterior] at hfront
  exact hfront.2 hp

end AffineIndependent

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_positive_face_centers_at_point (K : SimplicialComplex ℝ E)
    (s : K.faces) {p : E}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E))) :
    ∃ c : K.faces → E,
      (∀ t : K.faces, ∃ w : E → ℝ, (∀ v ∈ t.val, 0 < w v) ∧
        (∑ v ∈ t.val, w v) = 1 ∧ (∑ v ∈ t.val, w v • v) = c t) ∧ c s = p := by
  classical
  let c : K.faces → E := fun t => if t = s then p else t.val.centroid ℝ id
  refine ⟨c, ?_, by simp [c]⟩
  intro t
  by_cases hts : t = s
  · subst t
    simpa only [c, if_pos rfl] using
      (K.indep s.property).exists_positive_weights_of_mem_intrinsicInterior hp
  · have ht := K.nonempty_of_mem_faces t.property
    refine ⟨t.val.centroidWeights ℝ, ?_,
      t.val.sum_centroidWeights_eq_one_of_nonempty ℝ ht, ?_⟩
    · intro v _
      simp only [Finset.centroidWeights_apply, inv_pos]
      exact_mod_cast ht.card_pos
    · rw [show c t = t.val.centroid ℝ id from if_neg hts,
        Finset.centroid_eq_inv_card_smul_sum _ ht]
      simp only [Finset.centroidWeights_apply, Finset.smul_sum, id_eq]

end Geometry.SimplicialComplex
