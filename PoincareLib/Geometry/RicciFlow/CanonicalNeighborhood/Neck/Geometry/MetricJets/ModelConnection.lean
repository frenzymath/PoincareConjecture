import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Centered

/-!
# Uniform model connection derivatives along the cylinder

The standard Gram matrix and connection are invariant under axial
translations. Together with the common stereographic formula, this gives
one bound for their centered first derivatives. This is the model term
in the second-jet argument for Morgan--Tian Lemma A.2, pp. 497-498;
including the derivatives of the model connection acting on the metric error.

Adapted from Mapher `PoincareMT/Proofs/M25/AppA_1_Necks/ModelConnection.lean`
at commit `56d9cc710a322b1e69daa9353c1758b861c0e3fe`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace PoincareMT

/-- The literal cylinder Gram matrix of Definition 2.16, p. 30, is
unchanged by translation of the axial coordinate. -/
theorem roundCylinderGram_add_axial
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
  simpa only [roundCylinderGram_add_axial] using h.symm

/-- Axial translation also fixes the model connection coefficients used
in the covariant metric jets of Definition 2.16, p. 30. -/
theorem roundCylinderChristoffel_add_axial
    (u : ℝ) (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (s : ℝ)
    (a b d : Fin 3) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (p + (0, s)) a b d =
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d := by
  simp only [roundCylinderChristoffel, roundCylinderGram_add_axial,
    fderiv_roundCylinderGram_add_axial]

/-- The first model-connection derivative at a centered chart point is
independent of its axial coordinate, as required in Lemma A.2. -/
theorem fderiv_roundCylinderChristoffel_center_eq
    (q : UnitTwoSphere) (s : ℝ) (a b d : Fin 3) :
    fderiv ℝ (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) (0, s) =
    fderiv ℝ (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) 0 := by
  have h := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d)
    (x := (0 : RoundCylinderCoordinates)) (0, s)
  simpa only [roundCylinderChristoffel_add_axial, zero_add] using h.symm

/-- One positive constant controls the centered connection derivatives
for every chart and axial position in the model of Lemma A.2. -/
theorem exists_roundCylinderChristoffel_derivative_center_bound :
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
  rw [fderiv_roundCylinderChristoffel_center_eq,
    roundCylinderChristoffel_eq_chart_center 0 q₀ q]
  exact (Finset.single_le_sum (f := A) (fun _ _ => abs_nonneg _) (Finset.mem_univ
    (a, b, d, i))).trans (le_add_of_nonneg_left zero_le_one)

end PoincareMT
