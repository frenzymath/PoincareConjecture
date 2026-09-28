import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkProjection
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

section Combinatorial

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]




theorem card_add_card_le_of_mem_faceLink (K : SimplicialComplex 𝕜 E)
    {m : ℕ} (hbound : ∀ t ∈ K.faces, t.card ≤ m) (s : Finset E)
    {t : Finset E} (ht : t ∈ (K.faceLink s).faces) : s.card + t.card ≤ m := by
  have h := hbound (s ∪ t) ht.2.2
  rwa [Finset.card_union_of_disjoint ht.2.1] at h



theorem faceLink_faces_eq_empty_of_card_eq (K : SimplicialComplex 𝕜 E)
    {m : ℕ} (hbound : ∀ t ∈ K.faces, t.card ≤ m) {s : Finset E} (hs : s.card = m) :
    (K.faceLink s).faces = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h := K.card_add_card_le_of_mem_faceLink hbound s ht
  have htpos := Finset.card_pos.mpr ((K.faceLink s).nonempty_of_mem_faces ht)
  omega

omit [DecidableEq E] in



theorem exists_faces_eq_two_singletons (K : SimplicialComplex 𝕜 E)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 1) (hvertices : K.vertices.ncard = 2) :
    ∃ u v : E, u ≠ v ∧ K.faces = {({u} : Finset E), {v}} := by
  classical
  obtain ⟨u, v, huv, he⟩ := Set.ncard_eq_two.mp hvertices
  refine ⟨u, v, huv, ?_⟩
  ext t
  constructor
  · intro ht
    have htpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces ht)
    have htle := hbound t ht
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
    have hx : x ∈ K.vertices := ht
    rw [he] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · change u ∈ K.vertices
      rw [he]
      exact Or.inl rfl
    · change v ∈ K.vertices
      rw [he]
      exact Or.inr rfl

end Combinatorial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem finrank_faceDirection_of_card (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {n : ℕ} (hcard : s.card = n + 1) :
    Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction = n := by
  have h := (K.indep hs).finrank_vectorSpan (n := n) (by simpa using hcard)
  have hrange : range ((↑) : s → E) = (s : Set E) := by
    ext x
    simp
  rw [hrange] at h
  rw [direction_affineSpan]
  exact h

end Geometry.SimplicialComplex
