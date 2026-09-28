import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Centered

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture

theorem m25_roundCylinderGram_add_axial
    (u : ℝ) (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (s : ℝ) :
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) (p + (0, s)) =
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p := by
  ext a b
  simp only [roundCylinderGram_eq_stereographic_formula, Prod.fst_add, add_zero]

private theorem fderiv_roundCylinderGram_add_axial
    (u : ℝ) (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (s : ℝ)
    (a b : Fin 3) :
    fderiv ℝ (fun x => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) x a b) (p + (0, s)) =
    fderiv ℝ (fun x => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) x a b) p := by
  have h := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun x => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) x a b) (x := p) (0, s)
  simpa only [m25_roundCylinderGram_add_axial] using h.symm

theorem m25_roundCylinderChristoffel_add_axial
    (u : ℝ) (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (s : ℝ)
    (a b d : Fin 3) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (p + (0, s)) a b d =
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d := by
  simp only [roundCylinderChristoffel, m25_roundCylinderGram_add_axial,
    fderiv_roundCylinderGram_add_axial]

theorem m25_fderiv_roundCylinderChristoffel_center_eq
    (q : UnitTwoSphere) (s : ℝ) (a b d : Fin 3) :
    fderiv ℝ (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) (0, s) =
    fderiv ℝ (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) 0 := by
  have h := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d)
    (x := (0 : RoundCylinderCoordinates)) (0, s)
  simpa only [m25_roundCylinderChristoffel_add_axial, zero_add] using h.symm

theorem m25_exists_roundCylinderChristoffel_derivative_center_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : UnitTwoSphere) (s : ℝ) (a b d i : Fin 3),
      |fderiv ℝ (fun p => roundCylinderChristoffel 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) (0, s)
          (roundCylinderCoordinateBasis i)| ≤ D := by
  classical
  rcases isEmpty_or_nonempty UnitTwoSphere with he | hn
  · let := he
    exact ⟨1, zero_lt_one, fun q => isEmptyElim q⟩
  let q₀ : UnitTwoSphere := hn.some
  let A : Fin 3 × Fin 3 × Fin 3 × Fin 3 → ℝ := fun a =>
    |fderiv ℝ (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q₀) p a.1 a.2.1 a.2.2.1) 0
        (roundCylinderCoordinateBasis a.2.2.2)|
  refine ⟨1 + ∑ a, A a, by positivity, ?_⟩
  intro q s a b d i
  rw [m25_fderiv_roundCylinderChristoffel_center_eq,
    roundCylinderChristoffel_eq_chart_center 0 q₀ q]
  exact (Finset.single_le_sum (f := A) (fun _ _ => abs_nonneg _) (Finset.mem_univ
    (a, b, d, i))).trans (le_add_of_nonneg_left zero_le_one)

end PoincareConjecture
