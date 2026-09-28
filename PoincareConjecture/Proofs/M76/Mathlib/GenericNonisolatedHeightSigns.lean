import PoincareConjecture.Proofs.M76.Mathlib.FiniteHullHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph












set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






theorem mem_both_height_closures_of_generic_nonisolated
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices) {x : E}
    (hacc : x ∈ closure ((K.space ∩ {y | A y = A x}) \ {x})) :
    x ∈ closure (K.space ∩ {y | A y < A x}) ∧
      x ∈ closure (K.space ∩ {y | A x < A y}) := by
  classical
  let : Finite K.faces := hK.to_subtype
  let C (s : K.faces) : Set E :=
    (convexHull ℝ (s.val : Set E) ∩ {y | A y = A x}) \ {x}
  have hcover : ((K.space ∩ {y | A y = A x}) \ {x}) = ⋃ s : K.faces, C s := by
    ext y
    constructor
    · rintro ⟨⟨hyK, hyA⟩, hyx⟩
      obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hyK
      exact mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨hys, hyA⟩, hyx⟩
    · intro hy
      obtain ⟨s, hys⟩ := mem_iUnion.mp hy
      exact ⟨⟨K.convexHull_subset_space s.property hys.1.1, hys.1.2⟩, hys.2⟩
  rw [hcover, closure_iUnion_of_finite] at hacc
  obtain ⟨s, hxs⟩ := mem_iUnion.mp hacc
  have hx : x ∈ convexHull ℝ (s.val : Set E) := by
    apply (s.val.finite_toSet.isClosed_convexHull ℝ).closure_subset_iff.mpr
      (show C s ⊆ convexHull ℝ (s.val : Set E) from fun _ h => h.1.1)
    exact hxs
  obtain ⟨y, hy⟩ := closure_nonempty_iff.mp (nonempty_of_mem hxs)
  have hsverts : (s.val : Set E) ⊆ K.vertices := by
    intro v hv
    exact K.down_closed s.property (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)
  have hboth := s.val.mem_both_height_closures_of_distinct_level_points
    (K.nonempty_of_mem_faces s.property) A (hA.mono hsverts) hx hy.1.1
    (fun heq => hy.2 heq.symm) hy.1.2
  have hface := K.convexHull_subset_space s.property
  exact ⟨closure_mono (inter_subset_inter_left _ hface) hboth.1,
    closure_mono (inter_subset_inter_left _ hface) hboth.2⟩

end Geometry.SimplicialComplex
