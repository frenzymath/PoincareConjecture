import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineLevelComplexPosition
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProtectedCarrierRefinement

set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex

theorem exists_protected_affine_level_polyhedron_position
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (J P P₀ : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hP₀ : P₀.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space)
    (A : AffineSubspace ℝ E) (hPA : P.space ⊆ A)
    (L : ι → SimplicialComplex ℝ E) (hL : ∀ i, (L i).faces.Finite)
    (hLA : ∀ i, (L i).space ⊆ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ R K K₀ : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.IsSubdivision J ∧ K ≤ R ∧ K.space = P.space ∧
      K₀ ≤ K ∧ K₀.space = P₀.space ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces) ∧
      ∃ H : PLCarrierMotion J.space P₀.space ε,
        R.AffineOnFaces (H.map 1) ∧
        (∀ t x, H.map t x - x ∈ A.direction) ∧
        (∃ S : SimplicialComplex ℝ E,
          S.faces.Finite ∧ S.space = H.map 1 '' P.space) ∧
        ∀ i s, s ∈ K.faces → s ∉ K₀.faces → ∀ t, t ∈ (L i).faces →
          affineSpan ℝ (H.map 1 '' (s : Set E) ∪ (t : Set E)) = A ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (s : Set E))))
              (convexHull ℝ (t : Set E)) := by
  obtain ⟨R, K, K₀, Q, hR, hRJ, hK, hKs, hK₀, hK₀s,
    hfull, hQ, hQs, hfree⟩ :=
    J.exists_protected_carrier_refinement P P₀ hJ hP hP₀ hcv hP₀P hPJ hfront
  have hRs : R.space = J.space := hRJ.space_eq
  have hRcv : Convex ℝ R.space := hRs.symm ▸ hcv
  have hRQfront : frontier R.space ⊆ Q.space := by
    rw [hRs, hQs]
    exact subset_union_right
  have hK₀Q : K₀.space ⊆ Q.space := by
    rw [hK₀s, hQs]
    exact subset_union_left
  have hKA : K.space ⊆ A := by
    rw [hKs]
    exact hPA
  obtain ⟨H, hHaff, hHfixed, hHdir, hHfaces⟩ :=
    exists_protected_affine_level_complex_position R Q K K₀ hR hRcv hQ hRQfront hK
      hfull hK₀Q hfree A hKA L hL hLA hε
  let F : PLCarrierMotion J.space P₀.space ε :=
    { map := H.map
      continuous_map := H.continuous_map
      continuous_symm := H.continuous_symm
      zero := H.zero
      outside := by simpa only [hRs] using H.outside
      fixed_protected := fun t x hx => hHfixed t x (hK₀s.symm ▸ hx)
      carrier := by simpa only [hRs] using H.carrier
      finitePL := by
        rw [← hRs]
        exact H.finitePL
      small := H.small }
  refine ⟨R, K, K₀, hR, hRJ, hK, hKs, hK₀, hK₀s, hfull,
    F, hHaff, hHdir, ?_, hHfaces⟩
  have hKaff : K.AffineOnFaces (H.map 1) := fun s hs => hHaff s (hK hs)
  have hinj : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
  refine ⟨hKaff.embeddedImage hinj, hKaff.embeddedImage_finite hinj (hR.subset hK), ?_⟩
  rw [hKaff.embeddedImage_space hinj, hKs]

end Geometry.SimplicialComplex
