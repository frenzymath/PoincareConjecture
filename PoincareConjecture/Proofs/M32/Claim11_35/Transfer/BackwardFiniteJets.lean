import PoincareConjecture.Proofs.M32.Claim11_35.Evolving.Model
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.FiniteJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.M32

private noncomputable def backwardModelAdjustment (t : ℝ) (B : RoundCylinderTwoTensor) :
    RoundCylinderTwoTensor := fun z v w =>
  B z v w - EvolvingRoundCylinderMetric t z v w + EvolvingRoundCylinderMetric 0 z v w

private theorem backward_adjustment_coefficient (t : ℝ) (B : RoundCylinderTwoTensor)
    (q : UnitTwoSphere) (y : RoundCylinderCoordinates) (a b : Fin 3) :
    roundCylinderTensorCoefficient (backwardModelAdjustment t B)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b =
    roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
      roundCylinderGram t (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b := by
  simp only [roundCylinderGram, roundCylinderTensorCoefficient, backwardModelAdjustment]
  ring

private theorem backward_iterated_eq_zero {t : ℝ} (ht : t < 1)
    (q : UnitTwoSphere) (B : RoundCylinderTwoTensor) (k : ℕ) :
    roundCylinderIteratedDerivative t (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k =
      roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (backwardModelAdjustment t B) k := by
  induction k with
  | zero =>
    funext y a
    exact (backward_adjustment_coefficient t B q y (a 0) (a 1)).symm
  | succ k ih =>
    funext y a
    simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative, ih,
      evolving_roundCylinderChristoffel_eq_zero ht]

private theorem backward_center_norm_le_zero {t : ℝ} (ht : t ≤ 0)
    {r : ℕ} (q : UnitTwoSphere) (z : ℝ) (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared t (chartAt (EuclideanSpace ℝ (Fin 2)) q) (0, z) T ≤
      roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) (0, z) T := by
  have hden : 0 < 2 * (1 - t) := by linarith
  have hInv : (2 * (1 - t))⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) (by linarith)
  have hweight (i : Fin 3) :
      0 ≤ (![(2 * (1 - t))⁻¹, (2 * (1 - t))⁻¹, 1] : Fin 3 → ℝ) i ∧
      (![(2 * (1 - t))⁻¹, (2 * (1 - t))⁻¹, 1] : Fin 3 → ℝ) i ≤
        (![(2 * (1 - (0 : ℝ)))⁻¹, (2 * (1 - (0 : ℝ)))⁻¹, 1] : Fin 3 → ℝ) i := by
    fin_cases i <;> dsimp
    · exact ⟨inv_nonneg.mpr hden.le, by simpa using hInv⟩
    · exact ⟨inv_nonneg.mpr hden.le, by simpa using hInv⟩
    · exact ⟨zero_le_one, le_rfl⟩
  rw [evolving_roundCylinderTensorNormSquared_center (lt_of_le_of_lt ht zero_lt_one),
    evolving_roundCylinderTensorNormSquared_center (by norm_num : (0 : ℝ) < 1)]
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_right
    (Finset.prod_le_prod (fun i _ => (hweight (a i)).1) (fun i _ => (hweight (a i)).2))
    (sq_nonneg (T a))

private theorem backward_error_le_zero {t : ℝ} (ht : t ≤ 0)
    (B : RoundCylinderTwoTensor) (m : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared t B m z ≤
      roundCylinderJetErrorSquared 0 (backwardModelAdjustment t B) m z := by
  simp only [roundCylinderJetErrorSquared, sphere_chart_center]
  apply Finset.sum_le_sum
  intro k _
  rw [backward_iterated_eq_zero (lt_of_le_of_lt ht zero_lt_one)]
  exact backward_center_norm_le_zero ht _ _ _

theorem exists_backwardRoundCylinderJetErrorSquared_bound (R : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), t ∈ Icc (-1) 0 →
      ∀ (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace), z.2 ∈ Icc (-R) R →
      ∀ A : ℝ, 0 ≤ A →
      (∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
        roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
          roundCylinderGram t (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)) →
      (∀ j, j ≤ m → ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
            roundCylinderGram t (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ A) →
      roundCylinderJetErrorSquared t B m z ≤ C * A ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_roundCylinderJetErrorSquared_bound
    (isCompact_Icc : IsCompact (Icc (-R) R)) m
  refine ⟨C, hC, ?_⟩
  intro t ht B z hz A hA hs hjet
  apply (backward_error_le_zero ht.2 B m z).trans
  apply hbound (backwardModelAdjustment t B) z hz A hA
  · intro a b
    simpa only [backward_adjustment_coefficient] using hs a b
  · intro j hj a b
    simpa only [backward_adjustment_coefficient] using hjet j hj a b

end PoincareConjecture.M32
