import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMetricDifferences

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => E × E

local instance m64AutonomousDifference_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64AutonomousDifference_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64AutonomousDifference_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64AutonomousDifference_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1000000 in

theorem m64WeightedMetric_autonomous_difference_pointwise
    (w : Fin 2 → ℝ) (G0 G1 : E →L[ℝ] E →L[ℝ] ℝ)
    (T0 T1 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (q r j : P) (u : E)
    {kappa mu C Lambda h xi : ℝ} (hk : 0 < kappa) (hmu : 0 < mu)
    (hC : 0 ≤ C) (hw : ∀ i, mu ≤ w i ∧ w i ≤ Lambda)
    (hG : ‖G1‖ ≤ C) (hT : ‖T1‖ ≤ C)
    (hpos : ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G1 v v)
    (hh : h ≠ 0)
    (hDG : ‖G1 - G0‖ ≤ C * (|h| * ‖u‖))
    (hDT : ‖T1 - T0‖ ≤ C * (|h| * ‖u‖)) :
    let d := h⁻¹ • (q - r)
    let H := ‖q‖ ^ 2 + ‖r‖ ^ 2
    let nu := kappa * mu
    let K := 2 * Lambda * C
    nu / 2 * (xi ^ 2 * ‖d‖ ^ 2) ≤
      (h⁻¹ • (m64WeightedPairMetric w G1 q - m64WeightedPairMetric w G0 r))
        (xi ^ 2 • d + (2 * xi) • j) -
      (h⁻¹ • (m64WeightedQuadraticSource w T1 q - m64WeightedQuadraticSource w T0 r))
        (xi ^ 2 • u) +
      (32 * K ^ 2 / nu + 6 * K) *
        (H * xi ^ 2 * (1 + ‖u‖ ^ 2) + ‖j‖ ^ 2) := by
  let d := h⁻¹ • (q - r)
  let H := ‖q‖ ^ 2 + ‖r‖ ^ 2
  let nu := kappa * mu
  let K := 2 * Lambda * C
  let L0 := m64WeightedPairMetric w G0
  let L1 := m64WeightedPairMetric w G1
  let S0 := m64WeightedQuadraticSource w T0
  let S1 := m64WeightedQuadraticSource w T1
  let P0 := h⁻¹ • (L1 q - L1 r)
  let A0 := h⁻¹ • (L1 r - L0 r)
  let B0 := h⁻¹ • (S1 q - S1 r)
  let D0 := h⁻¹ • (S1 r - S0 r)
  have hnu : 0 < nu := mul_pos hk hmu
  have hLambda : 0 ≤ Lambda := hmu.le.trans ((hw 0).1.trans (hw 0).2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hw0 (i : Fin 2) : 0 ≤ w i ∧ w i ≤ Lambda :=
    ⟨hmu.le.trans (hw i).1, (hw i).2⟩
  have hratio : Lambda * C ≤ K := by dsimp [K]; nlinarith [mul_nonneg hLambda hC]
  have hcancel : |h⁻¹| * |h| = 1 := by simp [abs_inv, hh]
  have hd : ‖d‖ = |h⁻¹| * ‖q - r‖ := by simp [d, norm_smul]
  have hmono : nu * ‖d‖ ^ 2 ≤ P0 d := by
    have hm := mul_le_mul_of_nonneg_left
      (m64WeightedPairMetric_strong_monotone w G1 hk.le hmu.le hpos
        (fun i => (hw i).1) q r) (sq_nonneg h⁻¹)
    simpa only [d, P0, L1, nu, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      smul_apply, map_smul, smul_eq_mul] using
      (show kappa * mu * (h⁻¹ ^ 2 * ‖q - r‖ ^ 2) ≤
        h⁻¹ * (h⁻¹ * (L1 q - L1 r) (q - r)) by nlinarith)
  have hP : ‖P0‖ ≤ K * ‖d‖ := by
    calc
      _ = |h⁻¹| * ‖L1 q - L1 r‖ := by simp [P0, norm_smul]
      _ ≤ |h⁻¹| * (K * ‖q - r‖) := mul_le_mul_of_nonneg_left
        (m64WeightedPairMetric_gradient_bound w G1 hG hw0 q r) (abs_nonneg _)
      _ = _ := by rw [hd]; ring
  have hA : ‖A0‖ ≤ K * ‖r‖ * ‖u‖ := by
    have hb := mul_le_mul_of_nonneg_left
      (m64WeightedPairMetric_base_bound w G1 G0 hDG hw0 r) (abs_nonneg h⁻¹)
    have he : |h⁻¹| * (K * (|h| * ‖u‖) * ‖r‖) = K * ‖r‖ * ‖u‖ := by
      calc
        _ = (|h⁻¹| * |h|) * (K * ‖r‖ * ‖u‖) := by ring
        _ = _ := by rw [hcancel, one_mul]
    change |h⁻¹| * ‖L1 r - L0 r‖ ≤ _ at hb
    rw [he] at hb
    simpa only [A0, norm_smul, Real.norm_eq_abs] using hb
  have hB : ‖B0‖ ≤ K * (‖q‖ + ‖r‖) * ‖d‖ := by
    have hb := mul_le_mul_of_nonneg_left
      (m64WeightedQuadraticSource_gradient_bound w T1 hT hw0 q r) (abs_nonneg h⁻¹)
    have he : |h⁻¹| * ((Lambda * C) * (‖q‖ + ‖r‖) * ‖q - r‖) =
        (Lambda * C) * (‖q‖ + ‖r‖) * ‖d‖ := by rw [hd]; ring
    rw [he] at hb
    have hl : (Lambda * C) * (‖q‖ + ‖r‖) * ‖d‖ ≤ K * (‖q‖ + ‖r‖) * ‖d‖ := by gcongr
    simpa only [B0, S1, norm_smul, Real.norm_eq_abs] using hb.trans hl
  have hD : ‖D0‖ ≤ K * ‖r‖ ^ 2 * ‖u‖ := by
    have hb := mul_le_mul_of_nonneg_left
      (m64WeightedQuadraticSource_base_bound w T1 T0 hDT hw0 r) (abs_nonneg h⁻¹)
    have he : |h⁻¹| * ((Lambda * C) * (|h| * ‖u‖) * ‖r‖ ^ 2) =
        (Lambda * C) * ‖r‖ ^ 2 * ‖u‖ := by
      calc
        _ = (|h⁻¹| * |h|) * ((Lambda * C) * ‖r‖ ^ 2 * ‖u‖) := by ring
        _ = _ := by rw [hcancel, one_mul]
    rw [he] at hb
    have hl : (Lambda * C) * ‖r‖ ^ 2 * ‖u‖ ≤ K * ‖r‖ ^ 2 * ‖u‖ := by gcongr
    simpa only [D0, S0, S1, norm_smul, Real.norm_eq_abs] using hb.trans hl
  have hAsq : ‖A0‖ ^ 2 ≤ (2 * K) ^ 2 * H * (1 + ‖u‖ ^ 2) := by
    have ha := pow_le_pow_left₀ (norm_nonneg A0) hA 2
    have hr : ‖r‖ ^ 2 ≤ H := by dsimp [H]; nlinarith [sq_nonneg ‖q‖]
    have hm := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ K ^ 2 * ‖u‖ ^ 2)
    have hpos : 0 ≤ K ^ 2 * H := by dsimp [H]; positivity
    nlinarith
  have hBsq : ‖B0‖ ^ 2 ≤ (2 * K) ^ 2 * H * ‖d‖ ^ 2 := by
    have hb := pow_le_pow_left₀ (norm_nonneg B0) hB 2
    have hr : (‖q‖ + ‖r‖) ^ 2 ≤ 4 * H := by
      dsimp [H]
      nlinarith [sq_nonneg (‖q‖ - ‖r‖), sq_nonneg ‖q‖, sq_nonneg ‖r‖]
    have hm := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ K ^ 2 * ‖d‖ ^ 2)
    nlinarith
  have hDb : ‖D0‖ ≤ 2 * K * H * (1 + ‖u‖) := by
    apply hD.trans
    have hr : ‖r‖ ^ 2 ≤ H := by dsimp [H]; nlinarith [sq_nonneg ‖q‖]
    gcongr <;> nlinarith
  have hm := M60.suNaturalGrowth_dual_pointwise P0 A0 B0 D0 d j u
    (xi := xi) (W := 1) (H := H) hnu (show 0 ≤ 2 * K by positivity)
    zero_le_one (by dsimp [H]; positivity)
    (by simpa only [mul_one] using hmono)
    (by simp only [mul_one]; nlinarith [norm_nonneg d])
    (by simpa only [mul_one] using hAsq)
    (by simpa only [mul_one] using hBsq) hDb
  have hPA : P0 + A0 = h⁻¹ • (L1 q - L0 r) := by
    dsimp [P0, A0]
    rw [← smul_add]
    congr 1
    abel
  have hBD : B0 + D0 = h⁻¹ • (S1 q - S0 r) := by
    dsimp [B0, D0]
    rw [← smul_add]
    congr 1
    abel
  rw [hPA, hBD] at hm
  convert hm using 1 <;> ring

end PoincareConjecture
