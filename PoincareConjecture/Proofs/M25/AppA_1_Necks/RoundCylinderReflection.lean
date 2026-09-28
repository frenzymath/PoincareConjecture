import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Charts
import Mathlib.Analysis.Calculus.FDeriv.Equiv










set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture



noncomputable def roundCylinderCoordinateReflection :
    RoundCylinderCoordinates ≃L[ℝ] RoundCylinderCoordinates :=
  (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv


def roundCylinderAxialSign (i : Fin 3) : ℝ := if i = 2 then -1 else 1



theorem roundCylinderCoordinateReflection_basis (i : Fin 3) :
    roundCylinderCoordinateReflection (roundCylinderCoordinateBasis i) =
      roundCylinderAxialSign i • roundCylinderCoordinateBasis i := by
  fin_cases i <;> simp [roundCylinderCoordinateReflection, roundCylinderCoordinateBasis,
    roundCylinderAxialSign]



theorem roundCylinderCoordinateReflection_fderiv_apply
    (f : RoundCylinderCoordinates → ℝ) (a : ℝ)
    (p : RoundCylinderCoordinates) (i : Fin 3) :
    fderiv ℝ (fun x => a * f (roundCylinderCoordinateReflection x)) p
        (roundCylinderCoordinateBasis i) =
      a * roundCylinderAxialSign i * fderiv ℝ f
        (roundCylinderCoordinateReflection p) (roundCylinderCoordinateBasis i) := by
  change fderiv ℝ (a • (f ∘ roundCylinderCoordinateReflection)) p
    (roundCylinderCoordinateBasis i) = _
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply, smul_apply,
    roundCylinderCoordinateReflection.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, roundCylinderCoordinateReflection_basis, map_smul,
    smul_eq_mul]
  ring



theorem roundCylinderGram_axialReflection
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (a b : Fin 3) :
    roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b =
      roundCylinderAxialSign a * roundCylinderAxialSign b *
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          (roundCylinderCoordinateReflection p) a b := by
  fin_cases a <;> fin_cases b <;>
    simp [roundCylinderGram_eq_stereographic_formula, roundCylinderCoordinateReflection,
      roundCylinderCoordinateBasis, roundCylinderAxialSign]



theorem roundCylinderGram_inv_axialReflection
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (a b : Fin 3) :
    (roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p)⁻¹ a b =
      roundCylinderAxialSign a * roundCylinderAxialSign b *
        (roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          (roundCylinderCoordinateReflection p))⁻¹ a b := by
  have hdiag (x : RoundCylinderCoordinates) :
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) x =
        Matrix.diagonal ![32 / (‖x.1‖ ^ 2 + 4) ^ 2,
          32 / (‖x.1‖ ^ 2 + 4) ^ 2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [roundCylinderGram_eq_stereographic_formula, roundCylinderCoordinateBasis,
        Matrix.diagonal, EuclideanSpace.inner_single_left] <;> ring
  rw [hdiag, hdiag, Matrix.inv_diagonal, Matrix.inv_diagonal]
  fin_cases a <;> fin_cases b <;>
    simp [roundCylinderCoordinateReflection, roundCylinderAxialSign, Matrix.diagonal]



theorem roundCylinderChristoffel_axialReflection
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (a b d : Fin 3) :
    roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d =
      roundCylinderAxialSign a * roundCylinderAxialSign b * roundCylinderAxialSign d *
        roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          (roundCylinderCoordinateReflection p) a b d := by
  let G := roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
  let J := roundCylinderCoordinateReflection
  let σ := roundCylinderAxialSign
  have hσ (j : Fin 3) : σ j ^ 2 = 1 := by
    fin_cases j <;> norm_num [σ, roundCylinderAxialSign]
  have hD (i j k : Fin 3) :
      fderiv ℝ (fun x => G x i j) p (roundCylinderCoordinateBasis k) =
        σ i * σ j * σ k * fderiv ℝ (fun x => G x i j)
          (J p) (roundCylinderCoordinateBasis k) := by
    have hfun : (fun x => G x i j) = (fun x => σ i * σ j * G (J x) i j) := by
      funext x
      exact roundCylinderGram_axialReflection q x i j
    calc
      _ = fderiv ℝ (fun x => σ i * σ j * G (J x) i j) p
          (roundCylinderCoordinateBasis k) := congrArg
        (fun f : RoundCylinderCoordinates → ℝ =>
          fderiv ℝ f p (roundCylinderCoordinateBasis k)) hfun
      _ = _ := roundCylinderCoordinateReflection_fderiv_apply
        (fun x => G x i j) (σ i * σ j) p k
  change (1 / 2 : ℝ) * ∑ j : Fin 3, (G p)⁻¹ a j *
    (fderiv ℝ (fun x => G x d j) p (roundCylinderCoordinateBasis b) +
      fderiv ℝ (fun x => G x b j) p (roundCylinderCoordinateBasis d) -
      fderiv ℝ (fun x => G x b d) p (roundCylinderCoordinateBasis j)) =
    σ a * σ b * σ d * ((1 / 2 : ℝ) * ∑ j : Fin 3, (G (J p))⁻¹ a j *
      (fderiv ℝ (fun x => G x d j) (J p) (roundCylinderCoordinateBasis b) +
        fderiv ℝ (fun x => G x b j) (J p) (roundCylinderCoordinateBasis d) -
        fderiv ℝ (fun x => G x b d) (J p) (roundCylinderCoordinateBasis j)))
  calc
    _ = (1 / 2 : ℝ) * ∑ j : Fin 3, σ a * σ b * σ d * ((G (J p))⁻¹ a j *
        (fderiv ℝ (fun x => G x d j) (J p) (roundCylinderCoordinateBasis b) +
          fderiv ℝ (fun x => G x b j) (J p) (roundCylinderCoordinateBasis d) -
          fderiv ℝ (fun x => G x b d) (J p) (roundCylinderCoordinateBasis j))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [show (G p)⁻¹ a j = σ a * σ j * (G (J p))⁻¹ a j from
        roundCylinderGram_inv_axialReflection q p a j, hD, hD, hD]
      calc
        _ = σ j ^ 2 * (σ a * σ b * σ d * ((G (J p))⁻¹ a j *
            (fderiv ℝ (fun x => G x d j) (J p) (roundCylinderCoordinateBasis b) +
              fderiv ℝ (fun x => G x b j) (J p) (roundCylinderCoordinateBasis d) -
              fderiv ℝ (fun x => G x b d) (J p)
                (roundCylinderCoordinateBasis j)))) := by ring
        _ = _ := by rw [hσ, one_mul]
    _ = _ := by rw [← Finset.mul_sum]; ring

end PoincareConjecture
