import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeFaceCarrierBounds

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem exists_marked_full_surface_refinement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E]
    (J M : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hM : M.faces.Finite)
    (hMJ : M.space ⊆ J.space) (hbound : ∀ a ∈ M.faces, a.card ≤ 3)
    {p : E} (hpM : p ∈ M.space) (hpJ : p ∈ interior J.space) :
    ∃ K L : SimplicialComplex ℝ E,
      K.faces.Finite ∧ K.IsSubdivision J ∧ K.space = J.space ∧
      L ≤ K ∧ L.faces.Finite ∧ L.space = M.space ∧
      (∀ a ∈ K.faces, (∀ v ∈ a, v ∈ L.vertices) → a ∈ L.faces) ∧
      p ∈ K.vertices ∧ p ∈ L.vertices ∧ p ∈ interior K.space ∧
      (∀ a ∈ L.faces, a.card ≤ 3) ∧ (L.link p).space ⊆ (K.link p).space := by
  classical
  obtain ⟨D, hD, hDs, _⟩ := exists_finite_triangulation_iUnion_convexHull
    (fun _ : Unit => ({p} : Finset E)) (fun _ => affineIndependent_of_subsingleton ℝ _)
  have hDp : D.space = {p} := by simpa using hDs
  let B : Bool → SimplicialComplex ℝ E := fun b => if b then M else D
  have hB : ∀ b, (B b).faces.Finite := by
    intro b
    cases b <;> simp only [B, Bool.false_eq_true, ↓reduceIte]
    · exact hD
    · exact hM
  have hBJ : ∀ b, (B b).space ⊆ J.space := by
    intro b
    cases b <;> simp only [B, Bool.false_eq_true, ↓reduceIte]
    · rw [hDp]
      exact singleton_subset_iff.mpr (hMJ hpM)
    · exact hMJ
  obtain ⟨K, C, hK, hKJ, hC⟩ := J.exists_subdivision_with_finite_full_polyhedra hJ B hB hBJ
  let L := C true
  have hLK : L ≤ K := (hC true).1
  have hL : L.faces.Finite := hK.subset hLK
  have hLM : L.space = M.space := by simpa only [B, ↓reduceIte] using (hC true).2.1
  have hfull : ∀ a ∈ K.faces, (∀ v ∈ a, v ∈ L.vertices) → a ∈ L.faces := (hC true).2.2
  have hpoint : (C false).space = {p} := by
    simpa only [B, Bool.false_eq_true, ↓reduceIte, hDp] using (hC false).2.1
  have hpC : p ∈ (C false).space := hpoint.symm ▸ mem_singleton p
  obtain ⟨a, ha, _⟩ := mem_space_iff.mp hpC
  obtain ⟨v, hv⟩ := (C false).nonempty_of_mem_faces ha
  have hvp : v = p := hpoint.subset ((C false).subset_space ha hv)
  have hpK : p ∈ K.vertices := hvp ▸ K.down_closed ((hC false).1 ha)
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hpL : p ∈ L.vertices := by
    obtain ⟨a, ha, hpa⟩ := mem_space_iff.mp (hLM.symm.subset hpM)
    have hpin : p ∈ a := (K.vertex_mem_convexHull_iff hpK (hLK ha)).mp hpa
    exact L.down_closed ha (Finset.singleton_subset_iff.mpr hpin) (Finset.singleton_nonempty p)
  have hLb : ∀ a ∈ L.faces, a.card ≤ 3 := fun a ha =>
    L.face_card_le_of_hull_subset_finite_carrier M hM ha
      ((L.convexHull_subset_space ha).trans hLM.subset) hbound
  refine ⟨K, L, hK, hKJ, hKJ.space_eq, hLK, hL, hLM, hfull, hpK, hpL,
    by simpa only [hKJ.space_eq] using hpJ, hLb, ?_⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
  exact (K.link p).convexHull_subset_space ⟨hLK ha.1, ha.2.1, hLK ha.2.2⟩ hxa

end Geometry.SimplicialComplex
