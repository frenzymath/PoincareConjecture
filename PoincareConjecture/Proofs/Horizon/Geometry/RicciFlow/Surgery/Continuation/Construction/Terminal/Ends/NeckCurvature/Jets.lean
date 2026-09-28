import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Covariant

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.EpsilonNeck

local instance : Bundle.RiemannianBundle
    (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
  ⟨roundCylinderProductMetric.toRiemannianMetric⟩

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem normalized_pullback_covariant_component_sq_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {k : ℕ} (hk : k ≤ ⌊N.epsilon⁻¹⌋₊) (a : Fin (2 + k) → Fin 3) :
    (roundCylinderIteratedDerivative 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) N.normalized_pullback k (0, s) a) ^ 2 ≤
        (2 : ℝ) ^ (2 + k) * N.epsilon ^ 2 := by
  let b := roundCylinderChartBasis q
    (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s)
  let : FiniteDimensional ℝ
      (RoundCylinderTangent ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q), s)) :=
    Module.Finite.of_basis b
  let T := roundCylinderIteratedDerivative 0
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) N.normalized_pullback k
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s)
  have hGram : Matrix.of (fun i j => inner ℝ (b i) (b j)) =
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) := by
    ext i j
    simp only [Matrix.of_apply, b]
    rw [roundCylinderChartBasis_apply, roundCylinderChartBasis_apply]
    change roundCylinderProductMetric.inner _ _ _ = _
    exact roundCylinderChartFrame_gram q _ i j
  have hnorm := N.normalized_pullback_iterated_normSquared_lt (z := (q, s)) hs hk
  have hcontract :
      (∑ u : Fin (2 + k) → Fin 3, ∑ v : Fin (2 + k) → Fin 3,
        (∏ i, (Matrix.of (fun j l => inner ℝ (b j) (b l)))⁻¹ (u i) (v i)) *
          componentMultilinearMap T b (fun i => b (u i)) *
            componentMultilinearMap T b (fun i => b (v i))) ≤ N.epsilon ^ 2 := by
    rw [hGram]
    simpa only [componentMultilinearMap_basis, roundCylinderTensorNormSquared, T]
      using hnorm.le
  have h := abs_multilinear_apply_le_of_inverse_gram_contraction_le
    (componentMultilinearMap T b) b N.epsilon_pos.le hcontract (fun i => b (a i))
  simp only [componentMultilinearMap_basis] at h
  have hb (i : Fin 3) : ‖b i‖ ^ 2 ≤ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp only [b]
    rw [roundCylinderChartBasis_apply]
    change roundCylinderProductMetric.inner _ _ _ ≤ _
    rw [roundCylinderChartFrame_gram, roundCylinderGram_eq_stereographic_formula,
      sphere_chart_center]
    fin_cases i <;> norm_num [roundCylinderCoordinateBasis]
  have hprod : (∏ i : Fin (2 + k), ‖b (a i)‖) ^ 2 ≤ (2 : ℝ) ^ (2 + k) := by
    rw [← Finset.prod_pow]
    calc
      _ ≤ ∏ _i : Fin (2 + k), (2 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun i _ => hb (a i))
      _ = _ := by simp
  have hsq := mul_self_le_mul_self (abs_nonneg (T a)) h
  have hfinal : T a ^ 2 ≤ (2 : ℝ) ^ (2 + k) * N.epsilon ^ 2 := by
    have hprod' := mul_le_mul_of_nonneg_left hprod (sq_nonneg N.epsilon)
    nlinarith only [hsq, hprod', sq_abs (T a)]
  simpa only [T, sphere_chart_center] using hfinal

theorem abs_normalized_pullback_metric_component_le_two
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a : Fin 2 → Fin 3) :
    |roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      N.normalized_pullback 0 (0, s) a| ≤ 2 * N.epsilon := by
  have h := N.normalized_pullback_covariant_component_sq_le q hs (Nat.zero_le _) a
  norm_num only [Nat.add_zero, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) N.epsilon_pos.le)).mp (by
    rw [sq_abs]
    nlinarith only [h])

theorem abs_normalized_pullback_first_component_le_three
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a : Fin 3 → Fin 3) :
    |roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      N.normalized_pullback 1 (0, s) a| ≤ 3 * N.epsilon := by
  have h := N.normalized_pullback_covariant_component_sq_le q hs
    (Nat.le_trans (by decide : 1 ≤ 2) N.two_le_floor_inv_epsilon) a
  norm_num only [show (2 : ℝ) ^ (2 + 1) = 8 by norm_num] at h
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) N.epsilon_pos.le)).mp (by
    rw [sq_abs]
    nlinarith only [h, sq_nonneg N.epsilon])

theorem abs_normalized_pullback_second_component_le_four
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a : Fin 4 → Fin 3) :
    |roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      N.normalized_pullback 2 (0, s) a| ≤ 4 * N.epsilon := by
  have h := N.normalized_pullback_covariant_component_sq_le q hs
    N.two_le_floor_inv_epsilon a
  norm_num only [show (2 : ℝ) ^ (2 + 2) = 16 by norm_num] at h
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) N.epsilon_pos.le)).mp (by
    rw [sq_abs]
    nlinarith only [h])

end PoincareConjecture.EpsilonNeck
