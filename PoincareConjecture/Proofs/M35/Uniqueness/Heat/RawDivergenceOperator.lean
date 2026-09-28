import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawLowerOrder










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

def rawDivergenceCorrection (g : RiemannianMetric n V) (x : V) :
    (V →L[ℝ] V) →L[ℝ] V :=
  ∑ i, ∑ j, (fderiv ℝ (fun y => (rawCoordinateGram g y)⁻¹ i j) x (e i)) •
    (ContinuousLinearMap.apply ℝ V (e j))

@[simp] theorem rawDivergenceCorrection_apply (g : RiemannianMetric n V)
    (x : V) (L : V →L[ℝ] V) :
    rawDivergenceCorrection g x L = ∑ i, ∑ j,
      (fderiv ℝ (fun y => (rawCoordinateGram g y)⁻¹ i j) x (e i)) • L (e j) := by
  simp [rawDivergenceCorrection, ContinuousLinearMap.apply_apply]

theorem rawDivergenceCorrection_contDiff (g : RiemannianMetric n V) :
    ContDiff ℝ ∞ (rawDivergenceCorrection g) := by
  unfold rawDivergenceCorrection
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (((raw_inverseGram_entry_contDiff g i j).fderiv_right
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiff_const).smul contDiff_const

def rawDivergenceFirstOrder {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (x : V) : (V →L[ℝ] V) →L[ℝ] V :=
  rawFirstOrderCoefficient D x - rawDivergenceCorrection g x

theorem rawDivergenceFirstOrder_contDiff {g : RiemannianMetric n V}
    (D : LeviCivitaData g) : ContDiff ℝ ∞ (rawDivergenceFirstOrder D) :=
  (rawFirstOrderCoefficient_contDiff D).sub (rawDivergenceCorrection_contDiff g)

private theorem raw_divergence_term (g : RiemannianMetric n V)
    {X : V → V} (hX : ContDiff ℝ ∞ X) (x : V) (i j : Fin n) :
    fderiv ℝ (fun y => (rawCoordinateGram g y)⁻¹ i j • fderiv ℝ X y (e j)) x (e i) =
      (fderiv ℝ (fun y => (rawCoordinateGram g y)⁻¹ i j) x (e i)) • fderiv ℝ X x (e j) +
        (rawCoordinateGram g x)⁻¹ i j • fderiv ℝ (fderiv ℝ X) x (e i) (e j) := by
  have hA := (raw_inverseGram_entry_contDiff g i j).differentiable (by simp) x
  have hdX := (hX.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiable
    (by simp) x
  rw [fderiv_fun_smul hA (hdX.clm_apply (differentiableAt_const (e j))),
    fderiv_clm_apply hdX (differentiableAt_const (e j))]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_const_apply, zero_apply, map_zero, zero_add]
  exact add_comm _ _



theorem raw_vector_heat_divergence_operator {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X : V → V} (hX : ContDiff ℝ ∞ X) (x : V) :
    (∑ a, fieldHessian D X x (g.orthonormalBasis x a)
      (g.orthonormalBasis x a)) + rawRicciLinear D x (X x) =
      (∑ i, ∑ j, fderiv ℝ (fun y =>
        (rawCoordinateGram g y)⁻¹ i j • fderiv ℝ X y (e j)) x (e i)) +
          rawDivergenceFirstOrder D x (fderiv ℝ X x) + rawZeroOrderCoefficient D x (X x) := by
  rw [raw_vector_heat_full_coordinate_operator D hX]
  simp only [raw_divergence_term g hX, rawDivergenceFirstOrder, sub_apply,
    rawDivergenceCorrection_apply, Finset.sum_add_distrib]
  abel

end PoincareConjecture.M35.Uniqueness.Heat
