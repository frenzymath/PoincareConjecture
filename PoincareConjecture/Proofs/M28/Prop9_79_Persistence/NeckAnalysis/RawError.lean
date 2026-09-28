import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.AffineDifference
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.CovariantJetBounds
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.TensorNorms

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

open FiniteHessian

theorem exists_cylinderJetDifferenceSquared_bound
    {ι : Type*} (m : ℕ) (epsilon : ι → ℝ)
    (B C : ι → RoundCylinderTwoTensor) (z : ι → RoundCylinderSpace)
    (hB : ∀ i, RoundCylinderTensorSmoothOn (epsilon i) (B i))
    (hC : ∀ i, RoundCylinderTensorSmoothOn (epsilon i) (C i))
    (hz : ∀ i, (z i).2 ∈ Ioo (-(epsilon i)⁻¹) (epsilon i)⁻¹)
    (error : ι → ℝ) (herror : ∀ i, 0 < error i)
    (hraw : ∀ j ≤ m, ∀ i, ∀ a b : Fin 3,
      ‖iteratedFDeriv ℝ j (fun p =>
        roundCylinderTensorCoefficient (B i)
            (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1) p a b -
          roundCylinderTensorCoefficient (C i)
            (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1) p a b)
        (0, (z i).2)‖ ≤ error i) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i,
      cylinderJetDifferenceSquared 0 (B i) (C i) m (z i) ≤ L * error i ^ 2 := by
  classical
  let T := fun i => cylinderModelPlusDifference 0 (error i)⁻¹ (B i) (C i)
  have hT : ∀ i, RoundCylinderTensorSmoothOn (epsilon i) (T i) :=
    fun i => cylinderModelPlusDifference_smooth 0 _ (hB i) (hC i)
  have hp (i : ι) : (0, (z i).2) ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1).target ×ˢ
        Ioo (-(epsilon i)⁻¹) (epsilon i)⁻¹ := by
    refine ⟨?_, hz i⟩
    rw [← sphere_chart_center (z i).1]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1).map_source
      (mem_chart_source _ (z i).1)
  have hzero : ∀ a, HasUniformJetBoundsAt m
      (fun i p => roundCylinderIteratedDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1) (T i) 0 p a)
      (fun i => (0, (z i).2)) := by
    intro a j hj
    refine ⟨1, fun i => ?_⟩
    have hbc : ContDiffAt ℝ ∞ (fun p =>
        roundCylinderTensorCoefficient (B i)
            (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1) p (a 0) (a 1) -
          roundCylinderTensorCoefficient (C i)
            (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1) p (a 0) (a 1))
        (0, (z i).2) :=
      ((hB i _ _ _).sub (hC i _ _ _)).contDiffAt
        (((chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1).open_target.prod
          isOpen_Ioo).mem_nhds (hp i))
    change ‖iteratedFDeriv ℝ j (fun p => roundCylinderIteratedDerivative 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1)
      (cylinderModelPlusDifference 0 (error i)⁻¹ (B i) (C i)) 0 p a)
      (0, (z i).2)‖ ≤ 1
    simp_rw [cylinderModelPlusDifference_error_zero]
    change ‖iteratedFDeriv ℝ j (fun p => (error i)⁻¹ •
      (roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1) p (a 0) (a 1) -
        roundCylinderTensorCoefficient (C i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1) p (a 0) (a 1)))
      (0, (z i).2)‖ ≤ 1
    rw [iteratedFDeriv_const_smul_apply' (hbc.of_le (by exact_mod_cast le_top)),
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (herror i))]
    calc
      _ ≤ (error i)⁻¹ * error i :=
        mul_le_mul_of_nonneg_left (hraw j hj i _ _) (inv_nonneg.mpr (herror i).le)
      _ = 1 := inv_mul_cancel₀ (herror i).ne'
  have hjet := hasUniformJetBoundsAt_roundCylinderIteratedDerivative m epsilon
    (fun _ => 0) (fun _ => by norm_num) (fun i => (z i).1)
    (fun i => (z i).2) hz T hT hzero
  choose c hc0 hc using fun (k : Fin (m + 1)) (a : Fin (2 + k.val) → Fin 3) =>
    (hjet k.val (by omega) a).bound_all
  let L : ℝ := ∑ k : Fin (m + 1), ∑ a : Fin (2 + k.val) → Fin 3,
    cylinderTensorWeight 0 a * c k a ^ 2
  refine ⟨L, ?_, ?_⟩
  · exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun a _ =>
      mul_nonneg (cylinderTensorWeight_pos (by norm_num) a).le (sq_nonneg _)
  · intro i
    unfold cylinderJetDifferenceSquared
    dsimp only
    rw [← Fin.sum_univ_eq_sum_range]
    change (∑ k : Fin (m + 1), _) ≤ L * error i ^ 2
    dsimp only [L]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    rw [roundCylinderTensorNormSquared_eq_sum (by norm_num), Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    have hh := hc k a 0 (Nat.zero_le _) i
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hh
    change |roundCylinderIteratedDerivative 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1)
      (cylinderModelPlusDifference 0 (error i)⁻¹ (B i) (C i))
      k.val (0, (z i).2) a| ≤ c k a at hh
    rw [cylinderModelPlusDifference_iterated (by norm_num) _ (hB i) (hC i)
      (z i).1 k.val (0, (z i).2) (hp i), abs_mul, abs_inv,
      abs_of_pos (herror i)] at hh
    have hcomponent := (div_le_iff₀ (herror i)).mp
      (show |roundCylinderIteratedDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1) (B i) k.val (0, (z i).2) a -
        roundCylinderIteratedDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) (z i).1) (C i) k.val (0, (z i).2) a| /
          error i ≤ c k a by simpa only [div_eq_mul_inv, mul_comm] using hh)
    rw [sphere_chart_center]
    have hsquare := pow_le_pow_left₀ (abs_nonneg _) hcomponent 2
    rw [sq_abs, mul_pow] at hsquare
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsquare
      (cylinderTensorWeight_pos (by norm_num) a).le

private structure RawErrorDatum (m : ℕ) where
  epsilon : ℝ
  B : RoundCylinderTwoTensor
  C : RoundCylinderTwoTensor
  z : RoundCylinderSpace
  error : ℝ
  smooth_B : RoundCylinderTensorSmoothOn epsilon B
  smooth_C : RoundCylinderTensorSmoothOn epsilon C
  point_mem : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹
  error_pos : 0 < error
  raw_bound : ∀ j ≤ m, ∀ a b : Fin 3,
    ‖iteratedFDeriv ℝ j (fun p =>
      roundCylinderTensorCoefficient B
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) p a b -
        roundCylinderTensorCoefficient C
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) p a b)
      (0, z.2)‖ ≤ error

theorem exists_uniform_cylinderJetDifferenceSquared_bound (m : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (epsilon : ℝ) (B C : RoundCylinderTwoTensor),
      RoundCylinderTensorSmoothOn epsilon B →
      RoundCylinderTensorSmoothOn epsilon C →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ error : ℝ, 0 < error →
      (∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun p =>
          roundCylinderTensorCoefficient B
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) p a b -
            roundCylinderTensorCoefficient C
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) p a b)
          (0, z.2)‖ ≤ error) →
      cylinderJetDifferenceSquared 0 B C m z ≤ L * error ^ 2 := by
  obtain ⟨L, hL, hbound⟩ := exists_cylinderJetDifferenceSquared_bound m
    (RawErrorDatum.epsilon (m := m)) RawErrorDatum.B RawErrorDatum.C RawErrorDatum.z
    RawErrorDatum.smooth_B RawErrorDatum.smooth_C RawErrorDatum.point_mem
    RawErrorDatum.error RawErrorDatum.error_pos (fun _ hj i => i.raw_bound _ hj)
  refine ⟨L, hL, ?_⟩
  intro epsilon B C hB hC z hz error herror hraw
  exact hbound ⟨epsilon, B, C, z, error, hB, hC, hz, herror, hraw⟩

theorem exists_cylinder_raw_error_tolerance (m : ℕ) {delta : ℝ}
    (hdelta : 0 < delta) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ (epsilon : ℝ) (B C : RoundCylinderTwoTensor),
      RoundCylinderTensorSmoothOn epsilon B →
      RoundCylinderTensorSmoothOn epsilon C →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      (∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun p =>
          roundCylinderTensorCoefficient B
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) p a b -
            roundCylinderTensorCoefficient C
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) p a b)
          (0, z.2)‖ ≤ rho) →
      cylinderJetDifferenceSquared 0 B C m z ≤ delta := by
  obtain ⟨L, hL, hbound⟩ := exists_uniform_cylinderJetDifferenceSquared_bound m
  let rho := min 1 (delta / (L + 1))
  have hL1 : 0 < L + 1 := by linarith
  have hrho : 0 < rho := lt_min (by norm_num) (div_pos hdelta hL1)
  have hrho1 : rho ≤ 1 := min_le_left _ _
  have hbudget : (L + 1) * rho ≤ delta := by
    have h := mul_le_mul_of_nonneg_left (min_le_right 1 (delta / (L + 1))) hL1.le
    simpa only [mul_div_cancel₀ _ hL1.ne'] using h
  refine ⟨rho, hrho, ?_⟩
  intro epsilon B C hB hC z hz hraw
  apply (hbound epsilon B C hB hC z hz rho hrho hraw).trans
  have hsquare : rho ^ 2 ≤ rho := by nlinarith
  calc
    L * rho ^ 2 ≤ L * rho := mul_le_mul_of_nonneg_left hsquare hL
    _ ≤ (L + 1) * rho := by nlinarith
    _ ≤ delta := hbudget

theorem eventually_cylinderJetDifferenceSquared_of_raw_bounds
    {ι : Type*} (l : Filter ι) (m : ℕ)
    {epsilon : ℝ} {B C : ι → RoundCylinderTwoTensor}
    (hB : ∀ᶠ i in l, RoundCylinderTensorSmoothOn epsilon (B i))
    (hC : ∀ᶠ i in l, RoundCylinderTensorSmoothOn epsilon (C i))
    {delta : ℝ} (hdelta : 0 < delta)
    (hraw : ∀ rho : ℝ, 0 < rho → ∀ᶠ i in l, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ j ≤ m, ∀ a b : Fin 3,
      ‖iteratedFDeriv ℝ j (fun p =>
        roundCylinderTensorCoefficient (B i)
            (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) p a b -
          roundCylinderTensorCoefficient (C i)
            (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) p a b)
        (0, z.2)‖ ≤ rho) :
    ∀ᶠ i in l, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      cylinderJetDifferenceSquared 0 (B i) (C i) m z ≤ delta := by
  obtain ⟨rho, hrho, hpoint⟩ := exists_cylinder_raw_error_tolerance m hdelta
  filter_upwards [hB, hC, hraw rho hrho] with i hiB hiC hi z hz
  exact hpoint epsilon (B i) (C i) hiB hiC z hz (hi z hz)

end PoincareConjecture.Proofs.M28.NeckAnalysis
