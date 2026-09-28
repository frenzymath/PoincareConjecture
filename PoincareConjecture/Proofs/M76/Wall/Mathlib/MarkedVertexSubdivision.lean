import PoincareConjecture.Proofs.M76.Mathlib.AlignedHalfspaceFaces
import PoincareConjecture.Proofs.M76.Mathlib.SimplexHalfspaces

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem exists_subdivision_with_marked_vertices
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (S : Finset E)
    (hS : (S : Set E) ⊆ K.space) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      ∀ p ∈ S, p ∈ L.vertices := by
  classical
  choose H hH using fun p : E =>
    ({p} : Finset E).exists_affine_halfspaces_convexHull
      (affineIndependent_of_subsingleton ℝ _)
  have hpoint (p : E) : ({p} : Set E) = {x | ∀ A ∈ H p, A x ≤ 0} := by
    simpa only [Finset.coe_singleton, convexHull_singleton] using hH p
  let forms := S.biUnion H
  let n := hK.toFinset.sup Finset.card
  have hbound (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  obtain ⟨L, hL, hLK, _, hforms⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hK hbound forms
  refine ⟨L, hL, hLK, ?_⟩
  intro p hp
  have hpL : p ∈ L.space := hLK.space_eq.symm.subset (hS hp)
  have hpH : ∀ A ∈ H p, A p ≤ 0 := (hpoint p).subset (mem_singleton p)
  obtain ⟨s, hs, _, hverts⟩ := L.exists_face_in_halfspaces (H p)
    (fun A hA => hforms A (Finset.mem_biUnion.mpr ⟨p, hp, hA⟩)) hpL hpH
  have hsp : s = {p} := Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    ⟨L.nonempty_of_mem_faces hs, fun v hv =>
      (hpoint p).symm.subset (hverts v hv)⟩
  change {p} ∈ L.faces
  rwa [← hsp]

end Geometry.SimplicialComplex
