import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder.Reflection.Coordinates


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RoundCylinderReflection

variable (u : ℝ)
  (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))

theorem gram_reflect (p : RoundCylinderCoordinates) :
    roundCylinderGram u c (coordinates p) = roundCylinderGram u c p := rfl

theorem gram_parity (p : RoundCylinderCoordinates) (a b : Fin 3) :
    roundCylinderGram u c p a b =
      sign a * sign b * roundCylinderGram u c (coordinates p) a b := by
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) (c.symm p.1)).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1)
  change 2 * (1 - u) * inner ℝ (L (roundCylinderCoordinateBasis a).1)
      (L (roundCylinderCoordinateBasis b).1) +
      (roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2 =
    sign a * sign b * (2 * (1 - u) * inner ℝ (L (roundCylinderCoordinateBasis a).1)
      (L (roundCylinderCoordinateBasis b).1) +
      (roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2)
  fin_cases a <;> fin_cases b <;>
    simp [roundCylinderCoordinateBasis, sign]

theorem inverseGram_parity (p : RoundCylinderCoordinates) (a b : Fin 3) :
    (roundCylinderGram u c p)⁻¹ a b =
      sign a * sign b * (roundCylinderGram u c (coordinates p))⁻¹ a b := by
  let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal sign
  have hD : D⁻¹ = D := by
    dsimp only [D]
    rw [Matrix.inv_diagonal]
    congr 1
    exact Ring.inverse_unit
      ⟨sign, sign, funext sign_mul_self, funext sign_mul_self⟩
  have hG : roundCylinderGram u c p = D * roundCylinderGram u c (coordinates p) * D := by
    ext i j
    simpa [D, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc, mul_comm, mul_left_comm]
      using gram_parity u c p i j
  have hI := congrArg (fun G : Matrix (Fin 3) (Fin 3) ℝ => G⁻¹) hG
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hD] at hI
  have hab := congrArg (fun G : Matrix (Fin 3) (Fin 3) ℝ => G a b) hI
  simpa [D, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc, mul_comm, mul_left_comm]
    using hab

theorem gram_fderiv_parity (p : RoundCylinderCoordinates) (a b d : Fin 3) :
    fderiv ℝ (fun q => roundCylinderGram u c q a b) p (roundCylinderCoordinateBasis d) =
      sign a * sign b * sign d *
        fderiv ℝ (fun q => roundCylinderGram u c q a b)
          (coordinates p) (roundCylinderCoordinateBasis d) := by
  have hf : (fun q => roundCylinderGram u c q a b) =
      fun q => (sign a * sign b) * roundCylinderGram u c (coordinates q) a b :=
    funext fun q => gram_parity u c q a b
  conv_lhs => rw [hf]
  exact fderiv_const_mul_reflect (sign a * sign b)
    (fun q => roundCylinderGram u c q a b) p d

theorem christoffel_parity (p : RoundCylinderCoordinates) (a b d : Fin 3) :
    roundCylinderChristoffel u c p a b d =
      sign a * sign b * sign d * roundCylinderChristoffel u c (coordinates p) a b d := by
  unfold roundCylinderChristoffel
  rw [← mul_assoc (sign a * sign b * sign d),
    mul_comm (sign a * sign b * sign d) (1 / 2), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inverseGram_parity u c p a j, gram_fderiv_parity u c p d j b,
    gram_fderiv_parity u c p b j d, gram_fderiv_parity u c p b d j]
  ring_nf
  simp only [sign_sq, mul_one]

end PoincareConjecture.RoundCylinderReflection
