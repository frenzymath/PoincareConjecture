import PoincareConjecture.Proofs.M76.Mathlib.AlignedHalfspaceFaces
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finite_subdivision_with_vertices (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (P : Finset E) (hP : (P : Set E) ⊆ K.space) :
    ∃ D : SimplicialComplex ℝ E, D.faces.Finite ∧ D.IsSubdivision K ∧
      (P : Set E) ⊆ D.vertices := by
  classical
  let n := Module.finrank ℝ E
  let c : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let A (p : E) (i : Fin n) : E →ᵃ[ℝ] ℝ :=
    ((LinearMap.proj i).comp c.toLinearMap).toAffineMap - AffineMap.const ℝ E (c p i)
  let Hp (p : E) : Finset (E →ᵃ[ℝ] ℝ) :=
    Finset.univ.biUnion fun i : Fin n => {A p i, -A p i}
  let H := P.biUnion Hp
  let N := hK.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨D, hD, hDK, _, hDH⟩ := K.exists_subdivision_respectsAffineHyperplanes hK hN H
  refine ⟨D, hD, hDK, fun p hp => ?_⟩
  have hHD (B : E →ᵃ[ℝ] ℝ) (hB : B ∈ Hp p) : D.RespectsAffineHyperplane B :=
    hDH B (Finset.mem_biUnion.mpr ⟨p, hp, hB⟩)
  have hpH (B : E →ᵃ[ℝ] ℝ) (hB : B ∈ Hp p) : B p ≤ 0 := by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hB
    rcases Finset.mem_insert.mp hi with rfl | hi
    · change c p i - c p i ≤ 0
      simp
    · have he := Finset.mem_singleton.mp hi
      rw [he]
      change -(c p i - c p i) ≤ 0
      simp
  obtain ⟨s, hs, _, hverts⟩ := D.exists_face_in_halfspaces (Hp p) hHD
    (hDK.space_eq.symm ▸ hP hp) hpH
  have hsingle (v : E) (hv : v ∈ s) : v = p := by
    apply c.injective
    funext i
    have hplus : A p i ∈ Hp p := Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_insert_self _ _⟩
    have hminus : -A p i ∈ Hp p := Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    have hpv := hverts v hv (A p i) hplus
    have hmv := hverts v hv (-A p i) hminus
    change c v i - c p i ≤ 0 at hpv
    change -(c v i - c p i) ≤ 0 at hmv
    linarith
  obtain ⟨v, hv⟩ := D.nonempty_of_mem_faces hs
  have hvD : v ∈ D.vertices := by
    rw [vertices_eq]
    exact subset_biUnion_of_mem hs hv
  exact hsingle v hv ▸ hvD

end Geometry.SimplicialComplex
