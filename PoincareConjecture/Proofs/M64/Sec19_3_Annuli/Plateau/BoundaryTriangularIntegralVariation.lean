import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryBoundedCoefficientIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64TriangularSource_integral_firstVariation
    {A B : ℝ → LoopPlane → ℝ} {A0 B0 f g h : LoopPlane → ℝ} {C : ℝ}
    (hA : ∀ t p, |A t p| ≤ C) (hB : ∀ t p, |B t p| ≤ C)
    (hAm : ∀ t, AEStronglyMeasurable (A t) mu)
    (hBm : ∀ t, AEStronglyMeasurable (B t) mu)
    (hA0m : AEStronglyMeasurable A0 mu) (hB0m : AEStronglyMeasurable B0 mu)
    (hAl : ∀ p, Tendsto (fun t => A t p) (𝓝 0) (𝓝 (A0 p)))
    (hBl : ∀ p, Tendsto (fun t => B t p) (𝓝 0) (𝓝 (B0 p)))
    (hf : Integrable f mu) (hg : Integrable g mu) (hh : Integrable h mu) (r : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ p in S,
      (r * (1 + t * A t p) * f p + r⁻¹ * (1 + t * A t p)⁻¹ *
        ((t * B t p) ^ 2 * f p + (t * B t p) * g p + h p)) / 2)
      (∫ p in S, (r * (A0 p * f p) + r⁻¹ * (B0 p * g p - A0 p * h p)) / 2) 0 := by
  let q := fun (t : ℝ) (p : LoopPlane) => 1 + t * A t p
  let bb := fun (t : ℝ) (p : LoopPlane) => (q t p)⁻¹ * (B t p) ^ 2
  let b := fun (t : ℝ) (p : LoopPlane) => (q t p)⁻¹ * B t p
  let a := fun (t : ℝ) (p : LoopPlane) => (q t p)⁻¹ * A t p
  have hqm (t : ℝ) : AEStronglyMeasurable (q t) mu :=
    aestronglyMeasurable_const.add ((hAm t).const_mul t)
  have hbbm (t : ℝ) : AEStronglyMeasurable (bb t) mu :=
    (hqm t).inv₀.mul ((hBm t).pow 2)
  have hbm (t : ℝ) : AEStronglyMeasurable (b t) mu := (hqm t).inv₀.mul (hBm t)
  have ham (t : ℝ) : AEStronglyMeasurable (a t) mu := (hqm t).inv₀.mul (hAm t)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * C < 1 / 2 := by
    have hc : ContinuousAt (fun t : ℝ => |t| * C) 0 := continuous_abs.continuousAt.mul_const C
    exact hc.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| * C < 1 / 2))
  have hqpos {t : ℝ} (ht : |t| * C < 1 / 2) (p : LoopPlane) : 1 / 2 < q t p := by
    have hprod := mul_le_mul_of_nonneg_left (hA t p) (abs_nonneg t)
    rw [← abs_mul] at hprod
    have hlo := (abs_le.mp hprod).1
    dsimp only [q]
    linarith
  have hqi {t : ℝ} (ht : |t| * C < 1 / 2) (p : LoopPlane) : |(q t p)⁻¹| ≤ 2 := by
    have hp : 0 < q t p := lt_trans (by norm_num) (hqpos ht p)
    rw [abs_of_pos (inv_pos.mpr hp), inv_le_iff_one_le_mul₀ hp]
    linarith [hqpos ht p]
  have hbb {t : ℝ} (ht : |t| * C < 1 / 2) (p : LoopPlane) : |bb t p| ≤ 2 * C ^ 2 := by
    have hs : |B t p| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hB t p) 2
    dsimp only [bb]
    rw [abs_mul, abs_pow]
    exact mul_le_mul (hqi ht p) hs (sq_nonneg _) (by norm_num)
  have hb {t : ℝ} (ht : |t| * C < 1 / 2) (p : LoopPlane) : |b t p| ≤ 2 * C := by
    dsimp only [b]
    rw [abs_mul]
    exact mul_le_mul (hqi ht p) (hB t p) (abs_nonneg _) (by norm_num)
  have ha {t : ℝ} (ht : |t| * C < 1 / 2) (p : LoopPlane) : |a t p| ≤ 2 * C := by
    dsimp only [a]
    rw [abs_mul]
    exact mul_le_mul (hqi ht p) (hA t p) (abs_nonneg _) (by norm_num)
  have hA0 (p : LoopPlane) : |A0 p| ≤ C :=
    le_of_tendsto (hAl p).abs (Eventually.of_forall fun t => hA t p)
  have hB0 (p : LoopPlane) : |B0 p| ≤ C :=
    le_of_tendsto (hBl p).abs (Eventually.of_forall fun t => hB t p)
  have hqi_l (p : LoopPlane) : Tendsto (fun t => (q t p)⁻¹) (𝓝 0) (𝓝 1) := by
    have hqt : Tendsto (fun t => q t p) (𝓝 0) (𝓝 1) := by
      simpa only [zero_mul, add_zero, id_eq, q] using
        tendsto_const_nhds.add (tendsto_id.mul (hAl p))
    simpa only [inv_one] using hqt.inv₀ one_ne_zero
  have hbb_l (p : LoopPlane) : Tendsto (fun t => bb t p) (𝓝 0) (𝓝 ((B0 p) ^ 2)) := by
    simpa only [one_mul] using (hqi_l p).mul ((hBl p).pow 2)
  have hb_l (p : LoopPlane) : Tendsto (fun t => b t p) (𝓝 0) (𝓝 (B0 p)) := by
    simpa only [one_mul] using (hqi_l p).mul (hBl p)
  have ha_l (p : LoopPlane) : Tendsto (fun t => a t p) (𝓝 0) (𝓝 (A0 p)) := by
    simpa only [one_mul] using (hqi_l p).mul (hAl p)
  have hIA := m64BoundedCoefficient_integral_tendsto hAm hf
    (Eventually.of_forall hA) hAl
  have hIbb := m64BoundedCoefficient_integral_tendsto hbbm hf
    (hsmall.mono fun t ht => hbb ht) hbb_l
  have hIb := m64BoundedCoefficient_integral_tendsto hbm hg
    (hsmall.mono fun t ht => hb ht) hb_l
  have hIa := m64BoundedCoefficient_integral_tendsto ham hh
    (hsmall.mono fun t ht => ha ht) ha_l
  have iA (t : ℝ) := m64BoundedCoefficient_mul_integrable (hAm t) hf (hA t)
  have ibb {t : ℝ} (ht : |t| * C < 1 / 2) :=
    m64BoundedCoefficient_mul_integrable (hbbm t) hf (hbb ht)
  have ib {t : ℝ} (ht : |t| * C < 1 / 2) :=
    m64BoundedCoefficient_mul_integrable (hbm t) hg (hb ht)
  have ia {t : ℝ} (ht : |t| * C < 1 / 2) :=
    m64BoundedCoefficient_mul_integrable (ham t) hh (ha ht)
  have iA0 := m64BoundedCoefficient_mul_integrable hA0m hf hA0
  have iB0 := m64BoundedCoefficient_mul_integrable hB0m hg hB0
  have iH0 := m64BoundedCoefficient_mul_integrable hA0m hh hA0
  let J := fun (t : ℝ) (p : LoopPlane) =>
    (r * q t p * f p + r⁻¹ * (q t p)⁻¹ *
      ((t * B t p) ^ 2 * f p + (t * B t p) * g p + h p)) / 2
  let V := fun (t : ℝ) (p : LoopPlane) =>
    (r * (A t p * f p) + r⁻¹ * (t * (bb t p * f p) + b t p * g p - a t p * h p)) / 2
  let v := fun p : LoopPlane =>
    (r * (A0 p * f p) + r⁻¹ * (B0 p * g p - A0 p * h p)) / 2
  have isum {t : ℝ} (ht : |t| * C < 1 / 2) :
      Integrable (fun p => t * (bb t p * f p) + b t p * g p) mu := by
    convert! ((ibb ht).const_mul t).add (ib ht) using 1
  have iinner {t : ℝ} (ht : |t| * C < 1 / 2) :
      Integrable (fun p => t * (bb t p * f p) + b t p * g p - a t p * h p) mu := by
    convert! (isum ht).sub (ia ht) using 1
  have iV {t : ℝ} (ht : |t| * C < 1 / 2) : Integrable (V t) mu := by
    simpa only [Pi.add_apply] using
      (((iA t).const_mul r).add ((iinner ht).const_mul r⁻¹)).div_const 2
  have hIV {t : ℝ} (ht : |t| * C < 1 / 2) :
      (∫ p in S, V t p) =
        (r * (∫ p in S, A t p * f p) + r⁻¹ *
          (t * (∫ p in S, bb t p * f p) + (∫ p in S, b t p * g p) -
            (∫ p in S, a t p * h p))) / 2 := by
    dsimp only [V]
    have hs := integral_add ((iA t).const_mul r) ((iinner ht).const_mul r⁻¹)
    have hsub := integral_sub (isum ht) (ia ht)
    have hsum := integral_add ((ibb ht).const_mul t) (ib ht)
    rw [integral_div, hs,
      integral_const_mul, integral_const_mul,
      hsub, hsum, integral_const_mul]
  have hIv : (∫ p in S, v p) =
      (r * (∫ p in S, A0 p * f p) + r⁻¹ *
        ((∫ p in S, B0 p * g p) - (∫ p in S, A0 p * h p))) / 2 := by
    dsimp only [v]
    have hs := integral_add (iA0.const_mul r) ((iB0.sub iH0).const_mul r⁻¹)
    have hsub := integral_sub iB0 iH0
    simp only [Pi.sub_apply] at hs hsub
    rw [integral_div, hs, integral_const_mul, integral_const_mul, hsub]
  have hVlim : Tendsto (fun t => ∫ p in S, V t p) (𝓝 0) (𝓝 (∫ p in S, v p)) := by
    rw [hIv]
    have hl := ((hIA.const_mul r).add
      ((((tendsto_id.mul hIbb).add hIb).sub hIa).const_mul r⁻¹)).div_const (2 : ℝ)
    simp only [zero_mul, zero_add] at hl
    exact hl.congr' (hsmall.mono fun t ht => (hIV ht).symm)
  have iJ0 : Integrable (J 0) mu := by
    simpa only [J, q, zero_mul, add_zero, inv_one, mul_one, zero_pow (by norm_num : 2 ≠ 0),
      zero_add, Pi.add_apply] using ((hf.const_mul r).add (hh.const_mul r⁻¹)).div_const 2
  have hpoint {t : ℝ} (ht : |t| * C < 1 / 2) (p : LoopPlane) :
      J t p = J 0 p + t * V t p := by
    have hne : q t p ≠ 0 := (lt_trans (by norm_num) (hqpos ht p)).ne'
    dsimp only [J, V, a, b, bb, q] at hne ⊢
    simp only [zero_mul, add_zero, inv_one, mul_one, zero_pow (by norm_num : 2 ≠ 0),
      zero_add]
    field_simp [hne]
    ring
  change HasDerivAt (fun t => ∫ p in S, J t p) (∫ p in S, v p) 0
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (hVlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
  have hne : t ≠ 0 := ht0
  have hsplit : (∫ p in S, J t p) = (∫ p in S, J 0 p) + t * ∫ p in S, V t p := by
    simp_rw [hpoint ht]
    rw [integral_add iJ0 ((iV ht).const_mul t), integral_const_mul]
  simp only [slope, sub_zero, vsub_eq_sub, smul_eq_mul, hsplit, add_sub_cancel_left]
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end PoincareConjecture
