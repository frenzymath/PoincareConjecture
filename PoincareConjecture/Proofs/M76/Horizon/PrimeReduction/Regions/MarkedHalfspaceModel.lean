import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.LocalHalfspaceTraces
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralRefinement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_marked_local_halfspace_model
    {κ : Type*} [Finite κ] {A O R : Set V3}
    (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O)
    (hcharts : ∀ x ∈ O, ∃ Q : OpenPartialHomeomorph V3 V3,
      x ∈ Q.source ∧ LocallyPiecewiseAffineOn Q Q.source ∧
      (Q.source ⊆ interior R ∨
        ∃ (ell : V3 →ᴬ[ℝ] ℝ), ell.toAffineMap.linear ≠ 0 ∧
          ∀ y ∈ Q.source, y ∈ R ↔ 0 ≤ ell (Q y)))
    (P : κ → SimplicialComplex ℝ V3) (hP : ∀ i, (P i).faces.Finite) :
    ∃ (K : SimplicialComplex ℝ V3)
      (M : Sum Bool κ → SimplicialComplex ℝ V3),
      K.faces.Finite ∧ A ⊆ interior K.space ∧ K.space ⊆ O ∧
      (∀ i, M i ≤ K ∧ (M i).faces.Finite ∧
        ∀ f ∈ K.faces, (∀ v ∈ f, v ∈ (M i).vertices) → f ∈ (M i).faces) ∧
      (M (.inl false)).space = K.space ∩ R ∧
      (M (.inl true)).space = K.space ∩ frontier R ∧
      ∀ i, (M (.inr i)).space = K.space ∩ R ∩ (P i).space := by
  classical
  obtain ⟨C, hC, hAC, hCO⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed hA hO hAO
  obtain ⟨reg, fr, hreg, hfr, hregs, hfrs⟩ :=
    exists_finite_local_halfspace_traces C hC (fun x hx => hcharts x (hCO hx))
  have hclip (i : κ) : ∃ L : SimplicialComplex ℝ V3,
      L.faces.Finite ∧ L.space = C.space ∩ R ∩ (P i).space := by
    obtain ⟨L, hL, hLs⟩ := reg.exists_finite_triangulation_inter (P i) hreg (hP i)
    exact ⟨L, hL, hLs.trans (by rw [hregs])⟩
  choose L hL hLs using hclip
  let N : Sum Bool κ → SimplicialComplex ℝ V3 := fun i =>
    match i with
    | .inl false => reg
    | .inl true => fr
    | .inr j => L j
  have hN (i : Sum Bool κ) : (N i).faces.Finite := by
    rcases i with b | j
    · cases b
      · exact hreg
      · exact hfr
    · exact hL j
  have hNC (i : Sum Bool κ) : (N i).space ⊆ C.space := by
    rcases i with b | j
    · cases b
      · exact hregs.subset.trans inter_subset_left
      · exact hfrs.subset.trans inter_subset_left
    · exact (hLs j).subset.trans (inter_subset_left.trans inter_subset_left)
  obtain ⟨K, M, hK, hKC, hM⟩ :=
    C.exists_subdivision_with_finite_full_polyhedra hC N hN hNC
  refine ⟨K, M, hK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hKC.space_eq] using hAC
  · exact hKC.space_eq.subset.trans hCO
  · intro i
    exact ⟨(hM i).1, hK.subset (hM i).1, (hM i).2.2⟩
  · exact (hM (.inl false)).2.1.trans (hregs.trans (by rw [hKC.space_eq]))
  · exact (hM (.inl true)).2.1.trans (hfrs.trans (by rw [hKC.space_eq]))
  · intro i
    exact (hM (.inr i)).2.1.trans ((hLs i).trans (by rw [hKC.space_eq]))

end PoincareConjecture.M76
