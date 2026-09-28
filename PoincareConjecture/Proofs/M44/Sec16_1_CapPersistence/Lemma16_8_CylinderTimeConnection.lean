import PoincareConjecture.Proofs.M36.CylinderTwoJet
import PoincareConjecture.Proofs.M36.CylinderTensorNorm











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators Topology

namespace PoincareConjecture.M44

open M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates



theorem evolving_roundCylinderGram_chart (t : ℝ) (theta : UnitTwoSphere) (p : V) :
    roundCylinderGram t (chartAt E₂ theta) p =
      Matrix.diagonal ![(1 - t) * cylinderSphereFactor p,
        (1 - t) * cylinderSphereFactor p, 1] := by
  ext i j
  change 2 * (1 - t) * inner ℝ (E := E₃)
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm p.1)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm p.1
          (roundCylinderCoordinateBasis i).1))
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm p.1)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm p.1
          (roundCylinderCoordinateBasis j).1)) +
      (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 = _
  rw [sphere_chart_differential_inner_at]
  fin_cases i <;> fin_cases j <;>
    simp [roundCylinderCoordinateBasis, Matrix.diagonal, cylinderSphereFactor,
      EuclideanSpace.basisFun, EuclideanSpace.inner_single_left] <;> ring



theorem evolving_roundCylinderGram_entry (t : ℝ) (theta : UnitTwoSphere) (p : V)
    (i j : Fin 3) :
    roundCylinderGram t (chartAt E₂ theta) p i j =
      (1 - t) * cylinderSphereFactor p * cylinderHorizontalGram i j +
        (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 := by
  rw [evolving_roundCylinderGram_chart]
  fin_cases i <;> fin_cases j <;>
    simp [cylinderHorizontalGram, roundCylinderCoordinateBasis, Matrix.diagonal,
      EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]



theorem evolving_roundCylinderGram_contDiff (t : ℝ) (theta : UnitTwoSphere)
    (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p => roundCylinderGram t (chartAt E₂ theta) p i j) := by
  simp only [evolving_roundCylinderGram_entry]
  exact ((contDiff_const.mul cylinderSphereFactor_contDiff).mul contDiff_const).add
    contDiff_const



theorem evolving_roundCylinderGram_fderiv (t : ℝ) (theta : UnitTwoSphere) (p w : V)
    (i j : Fin 3) :
    fderiv ℝ (fun q => roundCylinderGram t (chartAt E₂ theta) q i j) p w =
      (1 - t) * ((-128 / (‖p.1‖ ^ 2 + 4) ^ 3) * inner ℝ p.1 w.1 *
        cylinderHorizontalGram i j) := by
  have heq : (fun q => roundCylinderGram t (chartAt E₂ theta) q i j) =
      fun q => (1 - t) * (cylinderSphereFactor q * cylinderHorizontalGram i j) +
        (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 := by
    funext q
    rw [evolving_roundCylinderGram_entry]
    ring
  have hd := (((cylinderSphereFactor_hasFDerivAt p).mul_const
    (cylinderHorizontalGram i j)).const_mul (1 - t)).add_const
      ((roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2)
  rw [heq]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun L : V →L[ℝ] ℝ => L w) hd.fderiv



theorem evolving_roundCylinderGram_inv {t : ℝ} (ht : t < 1)
    (theta : UnitTwoSphere) (p : V) :
    (roundCylinderGram t (chartAt E₂ theta) p)⁻¹ =
      Matrix.diagonal ![((1 - t) * cylinderSphereFactor p)⁻¹,
        ((1 - t) * cylinderSphereFactor p)⁻¹, 1] := by
  have htime : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  have hsphere : cylinderSphereFactor p ≠ 0 := by
    unfold cylinderSphereFactor
    positivity
  apply Matrix.inv_eq_left_inv
  rw [evolving_roundCylinderGram_chart, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, htime, hsphere, mul_assoc]

set_option maxHeartbeats 800000 in



theorem evolving_roundCylinderChristoffel_eq {t : ℝ} (ht : t < 1)
    (theta : UnitTwoSphere) (p : V) (a b d : Fin 3) :
    roundCylinderChristoffel t (chartAt E₂ theta) p a b d =
      roundCylinderChristoffel 0 (chartAt E₂ theta) p a b d := by
  have hne : ‖p.1‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  have htime : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  rw [roundCylinderChristoffel_chart]
  unfold roundCylinderChristoffel
  simp only [evolving_roundCylinderGram_inv ht, evolving_roundCylinderGram_fderiv]
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    simp [Matrix.diagonal, cylinderSphereFactor,
      cylinderChristoffelLinear, cylinderHorizontalCovector, cylinderHorizontalGram,
      roundCylinderCoordinateBasis, EuclideanSpace.basisFun, real_inner_comm] <;>
    field_simp [hne, htime] <;> ring



theorem evolving_roundCylinderTensorDerivative_eq {t : ℝ} (ht : t < 1)
    (theta : UnitTwoSphere) {r : ℕ} (T : V → (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorDerivative t (chartAt E₂ theta) T =
      roundCylinderTensorDerivative 0 (chartAt E₂ theta) T := by
  funext p a
  simp only [roundCylinderTensorDerivative, evolving_roundCylinderChristoffel_eq ht]

end PoincareConjecture.M44
