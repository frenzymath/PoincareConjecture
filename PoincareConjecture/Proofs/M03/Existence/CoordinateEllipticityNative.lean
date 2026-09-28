import PoincareConjecture.Proofs.M03.Existence.CoordinateMetricRegularityNative
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Set

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

theorem continuous_quadratic_joint :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) =>
      quadratic p.1 p.2) := by
  unfold quadratic
  fun_prop

theorem quadratic_smul_covector (G : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (xi : Fin n → ℝ) :
    quadratic G (a • xi) = a ^ 2 * quadratic G xi := by
  simp only [quadratic, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_sub_matrix (A G : Matrix (Fin n) (Fin n) ℝ)
    (xi : Fin n → ℝ) :
    quadratic (A - G) xi = quadratic A xi - quadratic G xi := by
  simp only [quadratic, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem norm_quadratic_le (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ) :
    ‖quadratic G xi‖ ≤ (n : ℝ) ^ 2 * ‖G‖ * ‖xi‖ ^ 2 := by
  have hterm (i j : Fin n) : ‖G i j * xi i * xi j‖ ≤ ‖G‖ * ‖xi‖ ^ 2 := by
    rw [norm_mul, norm_mul]
    calc
      ‖G i j‖ * ‖xi i‖ * ‖xi j‖ ≤ ‖G‖ * ‖xi‖ * ‖xi‖ := by
        exact mul_le_mul
          (mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm G)
            (norm_le_pi_norm xi i) (norm_nonneg _) (norm_nonneg _))
          (norm_le_pi_norm xi j) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  calc
    ‖quadratic G xi‖ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖G i j * xi i * xi j‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖G‖ * ‖xi‖ ^ 2 := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by simp [pow_two, mul_assoc]

theorem exists_uniform_quadratic_lower_bound {X : Type*} [TopologicalSpace X]
    (G : X → Matrix (Fin n) (Fin n) ℝ) {K : Set X} (hK : IsCompact K)
    (hG : ContinuousOn G K) (hpos : ∀ x ∈ K, (G x).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ xi : Fin n → ℝ,
      c * ‖xi‖ ^ 2 ≤ quadratic (G x) xi := by
  let S := K ×ˢ Metric.sphere (0 : Fin n → ℝ) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hcoeff : ContinuousOn (fun p : X × (Fin n → ℝ) => G p.1) S :=
    hG.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hQ : ContinuousOn (fun p : X × (Fin n → ℝ) => quadratic (G p.1) p.2) S :=
    continuous_quadratic_joint.comp_continuousOn
      (hcoeff.prodMk continuous_snd.continuousOn)
  have hpositive : ∀ p ∈ S, 0 < quadratic (G p.1) p.2 := by
    intro p hp
    apply quadratic_pos (G p.1) (hpos p.1 hp.1)
    intro hzero
    have hn : ‖p.2‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hp.2
    simp only [hzero, norm_zero] at hn
    norm_num at hn
  obtain ⟨c, hc, hbound⟩ := hS.exists_forall_le' hQ hpositive
  refine ⟨c, hc, ?_⟩
  intro x hx xi
  by_cases hxi : xi = 0
  · simp [hxi, quadratic]
  let eta : Fin n → ℝ := ‖xi‖⁻¹ • xi
  have heta : eta ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    simpa only [eta, Metric.mem_sphere, dist_zero_right, RCLike.ofReal_real_eq_id, id_eq] using
      (norm_smul_inv_norm (𝕜 := ℝ) hxi)
  have hscale : ‖xi‖ • eta = xi := by
    dsimp only [eta]
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hxi) xi
  have hhom := quadratic_smul_covector (G x) ‖xi‖ eta
  rw [hscale] at hhom
  calc
    c * ‖xi‖ ^ 2 ≤ quadratic (G x) eta * ‖xi‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hbound (x, eta) ⟨hx, heta⟩) (sq_nonneg _)
    _ = quadratic (G x) xi := (mul_comm _ _).trans hhom.symm

theorem continuousOn_inverse_posDef {X : Type*} [TopologicalSpace X]
    (G : X → Matrix (Fin n) (Fin n) ℝ) {K : Set X}
    (hG : ContinuousOn G K) (hpos : ∀ x ∈ K, (G x).PosDef) :
    ContinuousOn (fun x => (G x)⁻¹) K := by
  intro x hx
  exact (continuousAt_matrix_inv_of_posDef (G x) (hpos x hx)).comp_continuousWithinAt
    (hG x hx)

theorem exists_uniform_inverse_quadratic_lower_bound {X : Type*} [TopologicalSpace X]
    (G : X → Matrix (Fin n) (Fin n) ℝ) {K : Set X} (hK : IsCompact K)
    (hG : ContinuousOn G K) (hpos : ∀ x ∈ K, (G x).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ xi : Fin n → ℝ,
      c * ‖xi‖ ^ 2 ≤ quadratic (G x)⁻¹ xi :=
  exists_uniform_quadratic_lower_bound (fun x => (G x)⁻¹) hK
    (continuousOn_inverse_posDef G hG hpos) (fun x hx => (hpos x hx).inv)

theorem quadratic_lower_bound_of_close (G A : Matrix (Fin n) (Fin n) ℝ)
    {c : ℝ} (hc : 0 < c)
    (hG : ∀ xi : Fin n → ℝ, c * ‖xi‖ ^ 2 ≤ quadratic G xi)
    (hclose : ‖A - G‖ ≤ c / (2 * ((n : ℝ) + 1) ^ 2)) (xi : Fin n → ℝ) :
    (c / 2) * ‖xi‖ ^ 2 ≤ quadratic A xi := by
  have hden : 0 < 2 * ((n : ℝ) + 1) ^ 2 := by positivity
  have hdim : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hcoef : (n : ℝ) ^ 2 * ‖A - G‖ ≤ c / 2 := by
    calc
      (n : ℝ) ^ 2 * ‖A - G‖ ≤ (n : ℝ) ^ 2 * (c / (2 * ((n : ℝ) + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left hclose (sq_nonneg _)
      _ ≤ ((n : ℝ) + 1) ^ 2 * (c / (2 * ((n : ℝ) + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_right hdim (div_nonneg hc.le hden.le)
      _ = c / 2 := by
        have hn : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        <;> ring
  have herr : |quadratic A xi - quadratic G xi| ≤ (c / 2) * ‖xi‖ ^ 2 := by
    calc
      |quadratic A xi - quadratic G xi| = ‖quadratic (A - G) xi‖ := by
        rw [quadratic_sub_matrix, Real.norm_eq_abs]
      _ ≤ (n : ℝ) ^ 2 * ‖A - G‖ * ‖xi‖ ^ 2 := norm_quadratic_le _ _
      _ ≤ (c / 2) * ‖xi‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
  have hneg := (neg_le_abs (quadratic A xi - quadratic G xi)).trans herr
  linarith [hG xi]

theorem posDef_of_close_of_quadratic_lower_bound
    (G A : Matrix (Fin n) (Fin n) ℝ) {c : ℝ} (hc : 0 < c)
    (hG : ∀ xi : Fin n → ℝ, c * ‖xi‖ ^ 2 ≤ quadratic G xi)
    (hA : A.IsSymm) (hclose : ‖A - G‖ ≤ c / (2 * ((n : ℝ) + 1) ^ 2)) :
    A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa only [Matrix.isHermitian_iff_isSymm] using hA)
  intro xi hxi
  rw [← quadratic_eq_dotProduct]
  exact (mul_pos (div_pos hc (by norm_num)) (sq_pos_of_pos (norm_pos_iff.mpr hxi))).trans_le
    (quadratic_lower_bound_of_close G A hc hG hclose xi)

theorem exists_uniform_posDef_perturbation {X : Type*} [TopologicalSpace X]
    (G : X → Matrix (Fin n) (Fin n) ℝ) {K : Set X} (hK : IsCompact K)
    (hG : ContinuousOn G K) (hpos : ∀ x ∈ K, (G x).PosDef) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x ∈ K, ∀ A : Matrix (Fin n) (Fin n) ℝ,
      A.IsSymm → ‖A - G x‖ ≤ delta → A.PosDef := by
  obtain ⟨c, hc, hbound⟩ := exists_uniform_quadratic_lower_bound G hK hG hpos
  refine ⟨c / (2 * ((n : ℝ) + 1) ^ 2), by positivity, ?_⟩
  intro x hx A hA hclose
  exact posDef_of_close_of_quadratic_lower_bound (G x) A hc (hbound x hx) hA hclose

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem chartMetricCoefficients_continuousOn (g : RiemannianMetric n M) (p : M) :
    ContinuousOn (chartMetricCoefficients g p) (extChartAt (𝓡 n) p).target := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact (chartMetricCoefficients_contDiffOn g p i j).continuousOn

theorem exists_chartMetric_uniform_ellipticity (g : RiemannianMetric n M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ (extChartAt (𝓡 n) p).target) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ xi : Fin n → ℝ,
      c * ‖xi‖ ^ 2 ≤ quadratic (chartMetricCoefficients g p z)⁻¹ xi :=
  exists_uniform_inverse_quadratic_lower_bound (chartMetricCoefficients g p) hK
    ((chartMetricCoefficients_continuousOn g p).mono hKU)
    (fun z hz => chartMetricCoefficients_posDef g p (hKU hz))

theorem exists_chartMetric_uniform_posDef_perturbation
    (g : RiemannianMetric n M) (p : M) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ (extChartAt (𝓡 n) p).target) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ z ∈ K, ∀ A : Matrix (Fin n) (Fin n) ℝ,
      A.IsSymm → ‖A - chartMetricCoefficients g p z‖ ≤ delta → A.PosDef :=
  exists_uniform_posDef_perturbation (chartMetricCoefficients g p) hK
    ((chartMetricCoefficients_continuousOn g p).mono hKU)
    (fun z hz => chartMetricCoefficients_posDef g p (hKU hz))

theorem exists_chartMetric_inverse_norm_bound (g : RiemannianMetric n M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ (extChartAt (𝓡 n) p).target) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ K, ‖(chartMetricCoefficients g p z)⁻¹‖ ≤ B := by
  have hcont : ContinuousOn (fun z => (chartMetricCoefficients g p z)⁻¹) K :=
    continuousOn_inverse_posDef (chartMetricCoefficients g p)
      ((chartMetricCoefficients_continuousOn g p).mono hKU)
      (fun z hz => chartMetricCoefficients_posDef g p (hKU hz))
  obtain ⟨B, hB, hbound⟩ := (hK.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  exact ⟨B, hB, fun z hz => hbound _ ⟨z, hz, rfl⟩⟩

end PoincareConjecture.DeTurckNative

end
