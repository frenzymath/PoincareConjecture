import PoincareConjecture.Proofs.M76.Mathlib.ConvexFiniteAffineCover
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem face_card_le_of_finite_affine_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (T : Finset (AffineSubspace ℝ E)) {d : ℕ}
    (hd : ∀ A ∈ T, Module.finrank ℝ A.direction ≤ d)
    (hcover : ∀ x ∈ K.space, ∃ A ∈ T, x ∈ A)
    {a : Finset E} (ha : a ∈ K.faces) : a.card ≤ d + 1 := by
  classical
  have hcover' : convexHull ℝ (a : Set E) ⊆ ⋃ A : T, (A.val : Set E) := by
    intro x hx
    obtain ⟨A, hAT, hxA⟩ := hcover x (K.convexHull_subset_space ha hx)
    exact mem_iUnion.mpr ⟨⟨A, hAT⟩, hxA⟩
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ha
  have hne : (convexHull ℝ (a : Set E)).Nonempty :=
    ⟨v, subset_convexHull ℝ (a : Set E) hv⟩
  obtain ⟨A, hA⟩ := Convex.exists_subset_affineSubspace_of_subset_iUnion
    (convex_convexHull ℝ (a : Set E)) hne (fun A : T => A.val) hcover'
  have hvertices : Set.range ((↑) : a → E) ⊆ A.val := by
    rintro x ⟨w, rfl⟩
    exact hA (subset_convexHull ℝ (a : Set E) w.property)
  have hdir : vectorSpan ℝ (Set.range ((↑) : a → E)) ≤ A.val.direction :=
    vectorSpan_mono ℝ hvertices
  have hrank : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : a → E))) ≤ d :=
    (Submodule.finrank_mono hdir).trans (hd A.val A.property)
  have hcard := (K.indep ha).card_le_finrank_succ.trans (Nat.add_le_add_right hrank 1)
  simpa only [Fintype.card_coe] using hcard

end Geometry.SimplicialComplex
