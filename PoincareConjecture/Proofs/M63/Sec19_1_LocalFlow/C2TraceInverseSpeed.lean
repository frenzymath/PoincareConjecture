import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeedGradient
import Mathlib.Analysis.Calculus.MeanValue










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem curveSpeed_inverseSquared_hasDerivAt [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (v0 : ℝ) {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    HasDerivAt (fun y => (curveSpeed F c t y ^ 2)⁻¹ - (v0 ^ 2)⁻¹)
      (-2 * deriv (curveSpeed F c t) x / curveSpeed F c t x ^ 3) x := by
  have hv := (speed_pos F c hc ht x).ne'
  have hd := ((speed_contDiff F c hc ht).differentiable (by norm_num) x).hasDerivAt
  convert! ((hd.pow 2).inv (pow_ne_zero 2 hv)).sub_const ((v0 ^ 2)⁻¹) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring




theorem curveSpeed_inverseSquared_initial_bounds [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K R J v0 : ℝ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J) (hv0 : 0 < v0)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hInitial : ∀ y, curveSpeed F c a y = v0)
    (hCurv : ∀ r ∈ Ioo a b, ∀ y, m62CurvatureSquared F c r y ≤ R)
    (hJet : ∀ r ∈ Ioo a b, ∀ y,
      (F.metric r).tangentNorm (c y r) (m63CurvatureJet F c 1 r y) ≤
        J / Real.sqrt (r - a))
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    let v := curveSpeed F c t
    let η := fun y => (v y ^ 2)⁻¹ - (v0 ^ 2)⁻¹
    let B := K + R
    let m := v0 * Real.exp (-B * (b - a))
    let V := v0 * Real.exp (B * (b - a))
    |v x - v0| ≤ V * B * (t - a) ∧
      |η x| ≤ (2 * V * B / m ^ 3) * (t - a) ∧
      |deriv η x| ≤ (2 * V ^ 2 / m ^ 3) *
        ((K + 2 * K * Real.sqrt R) * (t - a) +
          4 * Real.sqrt R * J * Real.sqrt (t - a)) := by
  dsimp only
  let v := curveSpeed F c t
  let η := fun y => (v y ^ 2)⁻¹ - (v0 ^ 2)⁻¹
  let B := K + R
  let δ := b - a
  let τ := t - a
  let m := v0 * Real.exp (-B * δ)
  let V := v0 * Real.exp (B * δ)
  let Q := (K + 2 * K * Real.sqrt R) * τ + 4 * Real.sqrt R * J * Real.sqrt τ
  have hB : 0 ≤ B := add_nonneg hK hR
  have hδ : 0 ≤ δ := sub_nonneg.mpr (ht.1.trans ht.2)
  have hτ : 0 ≤ τ := sub_nonneg.mpr ht.1
  have hτδ : τ ≤ δ := sub_le_sub_right ht.2 a
  have hm : 0 < m := mul_pos hv0 (Real.exp_pos _)
  have hV : 0 < V := mul_pos hv0 (Real.exp_pos _)
  have hv : 0 < v x := speed_pos F c hc ht x
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hBδ : 0 ≤ B * δ := mul_nonneg hB hδ
  have hBτ : 0 ≤ B * τ := mul_nonneg hB hτ
  have hBτδ : B * τ ≤ B * δ := mul_le_mul_of_nonneg_left hτδ hB
  have hspeed := curveSpeed_exp_bounds F c hc hBounds x (fun r hr => hCurv r hr x)
    ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  rw [hInitial] at hspeed
  change v0 * Real.exp (-B * τ) ≤ v x ∧ v x ≤ v0 * Real.exp (B * τ) at hspeed
  have hvbounds : v x ∈ Icc m V := by
    constructor
    · exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (by nlinarith only [hBτδ])) hv0.le).trans hspeed.1
    · exact hspeed.2.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hBτδ) hv0.le)
  have hv0bounds : v0 ∈ Icc m V := by
    constructor
    · have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (show -B * δ ≤ 0 by nlinarith only [hBδ])) hv0.le
      simpa only [Real.exp_zero, mul_one] using h
    · have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hBδ) hv0.le
      simpa only [Real.exp_zero, mul_one] using h
  have hExp (z : ℝ) (hz : z ∈ Icc (-B * δ) (B * δ)) :
      |Real.exp z - 1| ≤ Real.exp (B * δ) * |z| := by
    have h := (convex_Icc (-B * δ) (B * δ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
      (fun y hy => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)] using
        Real.exp_le_exp.mpr hy.2)
      (show (0 : ℝ) ∈ Icc (-B * δ) (B * δ) by constructor <;> nlinarith only [hBδ]) hz
    simpa only [Real.norm_eq_abs, Real.exp_zero, sub_zero] using h
  have hplus := hExp (B * τ) ⟨by nlinarith only [hBδ, hBτ], hBτδ⟩
  have hminus := hExp (-B * τ)
    ⟨by nlinarith only [hBτδ], by nlinarith only [hBδ, hBτ]⟩
  rw [abs_of_nonneg hBτ] at hplus
  have hnegabs : |-B * τ| = B * τ := by
    rw [neg_mul, abs_neg, abs_of_nonneg hBτ]
  rw [hnegabs] at hminus
  have hspeedDiff : |v x - v0| ≤ V * B * τ := by
    apply abs_le.mpr
    constructor
    · have h := mul_le_mul_of_nonneg_left (abs_le.mp hminus).1 hv0.le
      dsimp only [V]
      nlinarith only [h, hspeed.1]
    · have h := mul_le_mul_of_nonneg_left (abs_le.mp hplus).2 hv0.le
      dsimp only [V]
      nlinarith only [h, hspeed.2]
  have hInvD (z : ℝ) (hz : z ∈ Icc m V) :
      HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-2 / z ^ 3) z := by
    have hz0 : z ≠ 0 := (hm.trans_le hz.1).ne'
    convert! ((hasDerivAt_id z).pow 2).inv (pow_ne_zero 2 hz0) using 1
    simp only [Pi.pow_apply, id_eq]
    field_simp
    ring
  have hInvBound (z : ℝ) (hz : z ∈ Icc m V) : ‖-2 / z ^ 3‖ ≤ 2 / m ^ 3 := by
    have hz0 : 0 < z := hm.trans_le hz.1
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hz0]
    norm_num only [abs_neg]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ hm.le hz.1 3)
  have hInv := (convex_Icc m V).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hInvD z hz).hasDerivWithinAt) hInvBound hv0bounds hvbounds
  have hη : |η x| ≤ (2 * V * B / m ^ 3) * τ := by
    change |(v x ^ 2)⁻¹ - (v0 ^ 2)⁻¹| ≤ _
    calc
      _ ≤ (2 / m ^ 3) * |v x - v0| := by simpa only [Real.norm_eq_abs] using hInv
      _ ≤ (2 / m ^ 3) * (V * B * τ) :=
        mul_le_mul_of_nonneg_left hspeedDiff (by positivity)
      _ = _ := by ring
  have hgrad : |deriv v x| ≤ V ^ 2 * Q :=
    curveSpeed_spatial_abs_bound F c hc hK hR hJ hv0 hBounds hInitial hCurv hJet ht x
  have hηgrad : |deriv η x| ≤ (2 * V ^ 2 / m ^ 3) * Q := by
    have hd := (curveSpeed_inverseSquared_hasDerivAt F c hc v0 ht x).deriv
    change deriv η x = -2 * deriv v x / v x ^ 3 at hd
    rw [hd, abs_div, abs_mul, abs_pow, abs_of_pos hv]
    norm_num only [abs_neg]
    calc
      2 * |deriv v x| / v x ^ 3 ≤ 2 * (V ^ 2 * Q) / v x ^ 3 := by
        gcongr
      _ ≤ 2 * (V ^ 2 * Q) / m ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hm.le hvbounds.1 3)
      _ = _ := by ring
  exact ⟨hspeedDiff, hη, hηgrad⟩

end PoincareConjecture.M63
