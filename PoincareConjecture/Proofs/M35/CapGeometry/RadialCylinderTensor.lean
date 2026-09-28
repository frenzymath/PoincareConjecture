import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetStability










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35


noncomputable def radialCylinderTensor (A : ℝ → ℝ) (b : ℝ) : RoundCylinderTwoTensor :=
  fun z v w => A z.2 / 2 * RoundCylinderMetric z v w +
    (b ^ 2 - A z.2 / 2) * v.2 * w.2

theorem radialCylinderTensor_apply (A : ℝ → ℝ) (b : ℝ)
    (z : RoundCylinderSpace) (v w : RoundCylinderTangent z) :
    radialCylinderTensor A b z v w =
      A z.2 * inner ℝ
        (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.val) z.1 v.1)
        (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.val) z.1 w.1) +
      b ^ 2 * v.2 * w.2 := by
  unfold radialCylinderTensor RoundCylinderMetric EvolvingRoundCylinderMetric
  ring

theorem radialCylinderTensor_coefficient (A : ℝ → ℝ) (b : ℝ)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (i j : Fin 3) :
    roundCylinderTensorCoefficient (radialCylinderTensor A b)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j =
        A p.2 / 2 * roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j +
          (b ^ 2 - A p.2 / 2) *
            (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 := rfl

theorem radialCylinderTensor_coefficient_error (A : ℝ → ℝ) (b : ℝ)
    (q q₀ : UnitTwoSphere) (p : RoundCylinderCoordinates) (i j : Fin 3) :
    roundCylinderTensorCoefficient (radialCylinderTensor A b)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j =
      (A p.2 - 2) *
        ((roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q₀) p i j -
          (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2) / 2) +
      (b ^ 2 - 1) * (roundCylinderCoordinateBasis i).2 *
        (roundCylinderCoordinateBasis j).2 := by
  rw [radialCylinderTensor_coefficient, roundCylinderGram_apply, roundCylinderGram_apply]
  ring

theorem radialCylinderTensor_coefficient_contDiffAt
    {A : ℝ → ℝ} (b : ℝ) (q : UnitTwoSphere) {p : RoundCylinderCoordinates}
    (hA : ContDiffAt ℝ ∞ A p.2) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient (radialCylinderTensor A b)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) y i j) p := by
  simp_rw [radialCylinderTensor_coefficient]
  have h := (hA.comp p contDiffAt_snd).div_const 2
  exact (h.mul (contDiff_roundCylinderGram 0 q i j).contDiffAt).add
    (((contDiffAt_const.sub h).mul contDiffAt_const).mul contDiffAt_const)

private theorem round_model_iterated_zero (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (n : ℕ) : roundCylinderIteratedDerivative u c (EvolvingRoundCylinderMetric u) n = 0 := by
  induction n with
  | zero =>
    funext p a
    exact sub_self _
  | succ n hn =>
    funext p a
    simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative, hn,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]
    convert! congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
      L (roundCylinderCoordinateBasis (a 0)))
      (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) p).fderiv using 1


theorem roundCylinderJetDifferenceSquared_model (u : ℝ) (B : RoundCylinderTwoTensor)
    (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetDifferenceSquared u B (EvolvingRoundCylinderMetric u) order z =
      roundCylinderJetErrorSquared u B order z := by
  unfold roundCylinderJetDifferenceSquared roundCylinderJetErrorSquared
  simp only [round_model_iterated_zero, Pi.zero_apply, sub_zero]

end PoincareConjecture.M35
