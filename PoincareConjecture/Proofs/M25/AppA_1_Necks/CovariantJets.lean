import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Centered










noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.EpsilonNeck

local instance m25RoundCylinderTangentRiemannianBundle : Bundle.RiemannianBundle
    (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
  ⟨roundCylinderProductMetric.toRiemannianMetric⟩

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}



theorem m25_abs_normalized_pullback_covariant_component_center_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {k : ℕ} (hk : k ≤ ⌊N.epsilon⁻¹⌋₊) (a : Fin (2 + k) → Fin 3) :
    |roundCylinderIteratedDerivative 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) N.normalized_pullback k (0, s) a| ≤
        (2 : ℝ) ^ (2 + k) * N.epsilon := by
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
    exact roundCylinderChartFrame_gram q
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) i j
  have hnorm := N.normalized_pullback_iterated_normSquared_lt (z := (q, s)) hs hk
  have hbound := abs_multilinear_apply_le_of_inverse_gram_contraction_le
    (componentMultilinearMap T b) b N.epsilon_pos.le
  have hcontract :
      (∑ u : Fin (2 + k) → Fin 3, ∑ v : Fin (2 + k) → Fin 3,
        (∏ i, (Matrix.of (fun j l => inner ℝ (b j) (b l)))⁻¹ (u i) (v i)) *
          componentMultilinearMap T b (fun i => b (u i)) *
            componentMultilinearMap T b (fun i => b (v i))) ≤ N.epsilon ^ 2 := by
    rw [hGram]
    simpa only [componentMultilinearMap_basis, roundCylinderTensorNormSquared, T]
      using hnorm.le
  have h := hbound hcontract (fun i => b (a i))
  simp only [componentMultilinearMap_basis] at h
  have hprod : (∏ i : Fin (2 + k), ‖b (a i)‖) ≤ (2 : ℝ) ^ (2 + k) := by
    calc
      _ ≤ ∏ _i : Fin (2 + k), (2 : ℝ) := Finset.prod_le_prod
        (fun _ _ => norm_nonneg _) (fun i _ =>
          norm_roundCylinderChartBasis_center_le_two q s (a i))
      _ = _ := by simp
  have hfinal := h.trans (mul_le_mul_of_nonneg_left hprod N.epsilon_pos.le)
  simpa only [T, sphere_chart_center, mul_comm] using hfinal

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in


theorem m25_two_le_floor_inv_epsilon (N : EpsilonNeck g) :
    2 ≤ ⌊N.epsilon⁻¹⌋₊ := by
  apply (Nat.le_floor_iff (inv_nonneg.mpr N.epsilon_pos.le)).mpr
  have h := N.epsilon_lt_half
  rw [← one_div, le_div_iff₀ N.epsilon_pos]
  norm_num
  linarith

end PoincareConjecture.EpsilonNeck
