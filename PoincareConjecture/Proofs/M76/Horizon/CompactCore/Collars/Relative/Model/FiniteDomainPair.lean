import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse







set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_finite_relative_frontier_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {D W : Set X}
    (hD : IsCompact D) (heD : PLDomain e D)
    (hW : IsCompact W) (heW : PLDomain e W) (hne : (D ∪ W).Nonempty) :
    ∃ (s : Finset (D ∪ W : Set X)) (F : X → (s → ℝ × V3)) (C : Set X)
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 4 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : C ≃ₜ K.space) (g : (s → ℝ × V3) → C),
      IsCompact C ∧ D ∪ W ⊆ interior C ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧
      (∀ i, A i ≤ K ∧ (A i).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A i).vertices) → t ∈ (A i).faces) ∧
      K.space = F '' C ∧ (A 0).space = F '' W ∧
      (A 1).space = F '' frontier W ∧
      (A 2).space = F '' (frontier D ∩ W) ∧
      (A 3).space = F '' (frontier D ∩ frontier W) ∧
      (A 2).space ∩ (A 1).space = (A 3).space ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      ∀ x ∈ C, ∃ (i : ι) (V : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V := by
  classical
  let : LocallyCompactSpace X := heD.locallyCompactSpace
  obtain ⟨s, F, C, K0, H0, hC, hDC, _, hK0, hFc, hF, hH0, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_neighborhood_model
      e heD.compatible heD.cover (hD.union hW) isOpen_univ (subset_univ _)
  have hDC' : D ⊆ C := fun x hx => interior_subset (hDC (Or.inl hx))
  have hWC : W ⊆ C := fun x hx => interior_subset (hDC (Or.inr hx))
  have hFinj : InjOn F C := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H0.injective (Subtype.ext
      ((hH0 ⟨x, hx⟩).trans (hxy.trans (hH0 ⟨y, hy⟩).symm))))
  have hK0s : K0.space = F '' C := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨H0.symm ⟨z, hz⟩, (H0.symm ⟨z, hz⟩).property,
        (hH0 (H0.symm ⟨z, hz⟩)).symm.trans
          (congrArg Subtype.val (H0.apply_symm_apply ⟨z, hz⟩))⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hH0 ⟨x, hx⟩]
      exact (H0 ⟨x, hx⟩).property
  obtain ⟨_, BD, _, _, _, hBD, _, hBDs, _, _⟩ :=
    OpenPartialHomeomorph.exists_finite_PL_domain_image_pair
      e heD.cover hFc hF hD (hFinj.mono hDC') heD.halfspace
  obtain ⟨PW, BW, _, hPW, _, hBW, hPWs, hBWs, _, _⟩ :=
    OpenPartialHomeomorph.exists_finite_PL_domain_image_pair
      e heW.cover hFc hF hW (hFinj.mono hWC) heW.halfspace
  have hFD : frontier D ⊆ C := heD.closed.frontier_subset.trans hDC'
  have hFW : frontier W ⊆ C := heW.closed.frontier_subset.trans hWC
  have himage (S T : Set X) (hS : S ⊆ C) (hT : T ⊆ C) :
      F '' (S ∩ T) = F '' S ∩ F '' T := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
    · rintro _ ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
      exact ⟨x, ⟨hx, hFinj (hT hy) (hS hx) hyx ▸ hy⟩, rfl⟩
  obtain ⟨PS, hPS, hPSs⟩ := BD.exists_finite_triangulation_inter PW hBD hPW
  obtain ⟨PQ, hPQ, hPQs⟩ := BD.exists_finite_triangulation_inter BW hBD hBW
  have hPSimage : PS.space = F '' (frontier D ∩ W) := by
    rw [hPSs, hBDs, hPWs, ← himage _ _ hFD hWC]
  have hPQimage : PQ.space = F '' (frontier D ∩ frontier W) := by
    rw [hPQs, hBDs, hBWs, ← himage _ _ hFD hFW]
  let J : Fin 4 → SimplicialComplex ℝ (s → ℝ × V3) := ![PW, BW, PS, PQ]
  have hJ : ∀ i, (J i).faces.Finite := by
    intro i
    fin_cases i
    · exact hPW
    · exact hBW
    · exact hPS
    · exact hPQ
  have hJK : ∀ i, (J i).space ⊆ K0.space := by
    intro i
    rw [hK0s]
    fin_cases i
    · exact hPWs ▸ image_mono hWC
    · exact hBWs ▸ image_mono hFW
    · exact hPSimage ▸ image_mono (inter_subset_left.trans hFD)
    · exact hPQimage ▸ image_mono (inter_subset_left.trans hFD)
  obtain ⟨K, A, hK, hKK0, hA⟩ :=
    K0.exists_subdivision_with_finite_full_polyhedra hK0 J hJ hJK
  let H := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  have hHF (x : C) : (H x : s → ℝ × V3) = F x := hH0 x
  obtain ⟨x, hx⟩ := hne
  let x0 : C := ⟨x, interior_subset (hDC hx)⟩
  obtain ⟨g, hgc, hg, hgPL⟩ :=
    exists_polyhedral_PL_model_inverse e K hK H F subset_rfl x0 hHF hproj
  have hA0 : (A 0).space = F '' W := (hA 0).2.1.trans hPWs
  have hA1 : (A 1).space = F '' frontier W := (hA 1).2.1.trans hBWs
  have hA2 : (A 2).space = F '' (frontier D ∩ W) := (hA 2).2.1.trans hPSimage
  have hA3 : (A 3).space = F '' (frontier D ∩ frontier W) := (hA 3).2.1.trans hPQimage
  have hmeet : (A 2).space ∩ (A 1).space = (A 3).space := by
    rw [hA2, hA1, hA3, ← himage _ _ (inter_subset_left.trans hFD) hFW]
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
      fun hx => ⟨⟨hx.1, heW.closed.frontier_subset hx.2⟩, hx.2⟩⟩
  exact ⟨s, F, C, K, A, H, g, hC, hDC, hFc, hF, hK,
    fun i => ⟨(hA i).1, hK.subset (hA i).1, (hA i).2.2⟩,
    hKK0.space_eq.trans hK0s, hA0, hA1, hA2, hA3, hmeet,
    hHF, hgc, hg, hgPL, hproj⟩

end PoincareConjecture.M76
