import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FaceStarSaturation










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem exists_properFace_of_mem_intrinsicFrontier (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {x : E}
    (hx : x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E))) :
    ∃ t ∈ K.faces, t ⊂ s ∧ x ∈ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨i, hi, hxi⟩ :=
    (AffineIndependent.mem_intrinsicFrontier_convexHull_finset
      (K.nonempty_of_mem_faces hs) (K.indep hs) x).mp hx
  have hne : (s.erase i).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hxi
  exact ⟨s.erase i, K.down_closed hs (Finset.erase_subset i s) hne,
    Finset.erase_ssubset hi, hxi⟩




theorem inter_subset_intrinsicFrontier_of_card_le (K : SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hne : t ≠ s) (hcard : t.card ≤ s.card) :
    convexHull ℝ (t : Set E) ∩ convexHull ℝ (s : Set E) ⊆
      intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  classical
  have hproper : t ∩ s ⊂ s := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro he
    have hst : s ⊆ t := he ▸ Finset.inter_subset_left
    exact hne (Finset.eq_of_subset_of_card_le hst hcard).symm
  intro x hx
  apply (K.indep hs).convexHull_subset_intrinsicFrontier hproper
  simpa only [Finset.coe_inter] using K.inter_subset_convexHull ht hs hx

end Geometry.SimplicialComplex
