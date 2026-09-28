import PoincareConjecture.Proofs.M76.Mathlib.AlignedHalfspaceFaces









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



def affineHalfspaceSubcomplex (K : SimplicialComplex ℝ E)
    (H : Finset (E →ᵃ[ℝ] ℝ)) : SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ ∀ v ∈ s, ∀ A ∈ H, A v ≤ 0}
  indep hs := K.indep hs.1
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht, fun v hv => hs.2 v (hts hv)⟩
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1



theorem affineHalfspaceSubcomplex_finite (K : SimplicialComplex ℝ E)
    (H : Finset (E →ᵃ[ℝ] ℝ)) (hK : K.faces.Finite) :
    (K.affineHalfspaceSubcomplex H).faces.Finite := hK.subset (fun _ hs => hs.1)




theorem affineHalfspaceSubcomplex_space (K : SimplicialComplex ℝ E)
    (H : Finset (E →ᵃ[ℝ] ℝ)) (hH : ∀ A ∈ H, K.RespectsAffineHyperplane A) :
    (K.affineHalfspaceSubcomplex H).space = K.space ∩ {x | ∀ A ∈ H, A x ≤ 0} := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    refine ⟨K.convexHull_subset_space hs.1 hxs, fun A hA => ?_⟩
    exact convexHull_min (fun v hv => hs.2 v hv A hA)
      ((convex_Iic (0 : ℝ)).affine_preimage A) hxs
  · rintro ⟨hxK, hxH⟩
    obtain ⟨s, hs, hxs, hverts⟩ := K.exists_face_in_halfspaces H hH hxK hxH
    exact mem_space_iff.mpr ⟨s, ⟨hs, hverts⟩, hxs⟩




theorem exists_finite_triangulation_inter_halfspaces [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (H : Finset (E →ᵃ[ℝ] ℝ)) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = K.space ∩ {x | ∀ A ∈ H, A x ≤ 0} := by
  classical
  let N := hK.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨R, hR, hRK, _, hRH⟩ := K.exists_subdivision_respectsAffineHyperplanes hK hN H
  exact ⟨R.affineHalfspaceSubcomplex H, R.affineHalfspaceSubcomplex_finite H hR,
    (R.affineHalfspaceSubcomplex_space H hRH).trans (by rw [hRK.space_eq])⟩

end Geometry.SimplicialComplex
