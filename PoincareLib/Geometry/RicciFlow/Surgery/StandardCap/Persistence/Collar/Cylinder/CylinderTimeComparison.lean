import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Cylinder.CylinderTimeConnection

/-!
# Time-zero error comparison for the evolving cylinder

Adding the difference between the static and evolving models preserves
the actual error tensor and its covariant derivatives. For nonnegative
times below one, the evolving inverse Gram controls the static norm.
Morgan--Tian, Proposition 12.7 in Proposition 16.5, pp. 373-374;
see M44 derivation 42.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators Topology

namespace PoincareMT.M44

open M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

/-- The horizontal inverse-Gram weights of the evolving cylinder.
Source: Proposition 12.7; M44 derivation 42. -/
noncomputable def evolvingCylinderInverseWeight (t : ℝ) : Fin 3 → ℝ :=
  ![(2 * (1 - t))⁻¹, (2 * (1 - t))⁻¹, 1]

/-- The static weights are no larger than the evolving weights for
nonnegative model time. Source: M44 derivation 42. -/
theorem cylinderInverseWeight_le_evolving {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1)
    (i : Fin 3) : cylinderInverseWeight i ≤ evolvingCylinderInverseWeight t i := by
  have hpos : 0 < 2 * (1 - t) := by positivity
  have h : (1 / 2 : ℝ) ≤ (2 * (1 - t))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hpos]
    linarith only [ht0]
  fin_cases i
  · exact h
  · exact h
  · exact le_rfl

/-- The actual evolving tensor norm is a sum of positive weighted
squares at the centered chart point. Source: M44 derivation 42. -/
theorem evolving_roundCylinderTensorNormSquared_center {t : ℝ} (ht : t < 1)
    {r : ℕ} (theta : UnitTwoSphere) (s : ℝ) (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared t (chartAt E₂ theta)
        (chartAt E₂ theta theta, s) T =
      ∑ a, (∏ i, evolvingCylinderInverseWeight t (a i)) * (T a) ^ 2 := by
  classical
  have hinv : (roundCylinderGram t (chartAt E₂ theta)
      (chartAt E₂ theta theta, s))⁻¹ = Matrix.diagonal (evolvingCylinderInverseWeight t) := by
    rw [evolving_roundCylinderGram_inv ht, sphere_chart_center_zero]
    congr 1
    ext i
    fin_cases i <;> norm_num [cylinderSphereFactor, evolvingCylinderInverseWeight, mul_comm]
  unfold roundCylinderTensorNormSquared
  rw [hinv]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · rw [diagonal_tensor_product, if_pos rfl]
    ring
  · intro b _ hba
    rw [diagonal_tensor_product, if_neg (Ne.symm hba), zero_mul, zero_mul]
  · simp

/-- Every static covariant norm is bounded by the evolving norm of
the same tensor. Source: Proposition 12.7; M44 derivation 42. -/
theorem roundCylinderTensorNormSquared_zero_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1)
    {r : ℕ} (theta : UnitTwoSphere) (s : ℝ) (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared 0 (chartAt E₂ theta)
        (chartAt E₂ theta theta, s) T ≤
      roundCylinderTensorNormSquared t (chartAt E₂ theta)
        (chartAt E₂ theta theta, s) T := by
  rw [roundCylinderTensorNormSquared_center, evolving_roundCylinderTensorNormSquared_center ht]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Finset.prod_le_prod
    (fun i _ => (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans (cylinderInverseWeight_bounds _).1)
    (fun i _ => cylinderInverseWeight_le_evolving ht0 ht (a i))

/-- The auxiliary tensor has exactly the original error relative to
the evolving model. It does not replace the physical metric.
Source: the cylinder comparison in M44 derivation 42. -/
noncomputable def staticCylinderCorrection (t : ℝ) (B : RoundCylinderTwoTensor) :
    RoundCylinderTwoTensor :=
  fun z v w => B z v w + EvolvingRoundCylinderMetric 0 z v w -
    EvolvingRoundCylinderMetric t z v w

/-- The correction acts linearly on literal chart coefficients.
Source: Proposition 12.7; M44 derivation 42. -/
theorem staticCylinderCorrection_coefficient (t : ℝ) (B : RoundCylinderTwoTensor)
    (c : OpenPartialHomeomorph UnitTwoSphere E₂) (p : V) (a b : Fin 3) :
    roundCylinderTensorCoefficient (staticCylinderCorrection t B) c p a b =
      roundCylinderTensorCoefficient B c p a b + roundCylinderGram 0 c p a b -
        roundCylinderGram t c p a b := rfl

/-- Every covariant error jet agrees, since the actual model
connections agree. Source: M44 derivation 42. -/
theorem staticCylinderCorrection_iteratedDerivative {t : ℝ} (ht : t < 1)
    (B : RoundCylinderTwoTensor) (theta : UnitTwoSphere) (k : ℕ) :
    roundCylinderIteratedDerivative 0 (chartAt E₂ theta) (staticCylinderCorrection t B) k =
      roundCylinderIteratedDerivative t (chartAt E₂ theta) B k := by
  induction k with
  | zero =>
      funext p a
      simp only [roundCylinderIteratedDerivative, staticCylinderCorrection_coefficient]
      ring
  | succ k ih =>
      simp only [roundCylinderIteratedDerivative, ih, evolving_roundCylinderTensorDerivative_eq ht]

/-- The complete squared intrinsic error decreases under the static
correction at nonnegative times below one. Source: M44 derivation 42. -/
theorem staticCylinderCorrection_jetError_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1)
    (B : RoundCylinderTwoTensor) (k : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared 0 (staticCylinderCorrection t B) k z ≤
      roundCylinderJetErrorSquared t B k z := by
  unfold roundCylinderJetErrorSquared
  simp only [staticCylinderCorrection_iteratedDerivative ht]
  exact Finset.sum_le_sum (fun j _ =>
    roundCylinderTensorNormSquared_zero_le ht0 ht z.1 z.2 _)

/-- A genuine evolving comparison supplies a genuine static
comparison for its corrected error tensor, with the same tolerance
and finite order. Source: Proposition 12.7; M44 derivation 42. -/
theorem staticCylinderCorrection_close {t epsilon : ℝ} (ht0 : 0 ≤ t) (ht : t < 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon t B) :
    RoundCylinderClose epsilon 0 (staticCylinderCorrection t B) := by
  refine ⟨?_, ?_⟩
  · intro theta a b
    simp only [staticCylinderCorrection_coefficient]
    exact ((hB.1 theta a b).add
      (evolving_roundCylinderGram_contDiff 0 theta a b).contDiffOn).sub
        (evolving_roundCylinderGram_contDiff t theta a b).contDiffOn
  · obtain ⟨bound, hbound, hjets⟩ := hB.2
    exact ⟨bound, hbound, fun z hz =>
      (staticCylinderCorrection_jetError_le ht0 ht B _ z).trans (hjets z hz)⟩

end PoincareMT.M44
