import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceModel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt









set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower



theorem radial_estimates :
    let r0 : ℝ := Real.sqrt 15 / 4
    let r1 : ℝ := Real.sqrt 4095 / 64
    let U : ℝ → ℝ → ℝ := fun t r =>
      r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
    let D : ℝ → ℝ → ℝ := fun t r =>
      2 * r - r / Real.sqrt (1 - r ^ 2) + t / 32
    3 / 4 < r0 ∧ r0 < r1 ∧ r1 < 1 ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => U p.1 p.2)
      (Set.univ ×ˢ Set.Ioo (-1) 1) ∧
    (∀ t r : ℝ, r ∈ Set.Ioo (-1) 1 → HasDerivAt (U t) (D t r) r) ∧
    ∀ t ∈ Set.Ioo (-3 / 2 : ℝ) (3 / 2),
      (∀ r ∈ Set.Icc (0 : ℝ) (1 / 4), U t r < 267 / 256) ∧
      137 / 128 < U t (1 / 2) ∧
      (∀ r ∈ Set.Icc (1 / 4 : ℝ) (3 / 4), 17 / 320 < D t r) ∧
      StrictMonoOn (U t) (Set.Icc (1 / 4 : ℝ) (3 / 4)) ∧
      (∀ r ∈ Set.Icc (3 / 4 : ℝ) r0, 73 / 64 < U t r) ∧
      (∀ r ∈ Set.Ico r0 (1 : ℝ), D t r < -93 / 64) ∧
      StrictAntiOn (U t) (Set.Icc r0 (1 : ℝ)) ∧
      U t r1 < 4351 / 4096 := by
  let r0 : ℝ := Real.sqrt 15 / 4
  let r1 : ℝ := Real.sqrt 4095 / 64
  let U : ℝ → ℝ → ℝ := fun t r =>
    r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
  let D : ℝ → ℝ → ℝ := fun t r =>
    2 * r - r / Real.sqrt (1 - r ^ 2) + t / 32
  change 3 / 4 < r0 ∧ r0 < r1 ∧ r1 < 1 ∧ _
  have h0 : 0 < r0 := by dsimp only [r0]; positivity
  have h1 : 0 < r1 := by dsimp only [r1]; positivity
  have h0sq : r0 ^ 2 = 15 / 16 := by
    dsimp only [r0]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
    norm_num
  have h1sq : r1 ^ 2 = 4095 / 4096 := by
    dsimp only [r1]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4095)]
    norm_num
  have h0lower : (3 / 4 : ℝ) < r0 := by nlinarith only [h0, h0sq]
  have h01 : r0 < r1 := by nlinarith only [h0, h1, h0sq, h1sq]
  have h1upper : r1 < 1 := by nlinarith only [h1, h1sq]
  have h0upper : r0 < 1 := h01.trans h1upper
  have h0fine : r0 < 31 / 32 := by nlinarith only [h0, h0sq]
  have hrad (r : ℝ) (hr : r ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - r ^ 2 := by
    have hp : 0 < (1 - r) * (r + 1) :=
      mul_pos (sub_pos.mpr hr.2) (by linarith only [hr.1])
    nlinarith only [hp]
  have hradClosed (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      (Real.sqrt (1 - r ^ 2)) ^ 2 = 1 - r ^ 2 := by
    apply Real.sq_sqrt
    nlinarith only [sq_nonneg r, hr.1, hr.2]
  have hsmooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => U p.1 p.2)
      (univ ×ˢ Ioo (-1 : ℝ) 1) := by
    have hp : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2 ^ 2) := contDiff_snd.pow 2
    have ha : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.sqrt (1 - p.2 ^ 2))
        (univ ×ˢ Ioo (-1 : ℝ) 1) :=
      (contDiff_const.sub hp).contDiffOn.sqrt (fun p hp => (hrad p.2 hp.2).ne')
    exact (hp.contDiffOn.add ha).add
      ((contDiff_snd.mul contDiff_fst).div_const 32).contDiffOn
  have hderiv (t r : ℝ) (hr : r ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt (U t) (D t r) r := by
    have hs : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
      convert! (hasDerivAt_id r).pow 2 using 1
      simp
    have ha : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
        ((-2 * r) / (2 * Real.sqrt (1 - r ^ 2))) r := by
      simpa only [neg_mul] using (hs.const_sub (1 : ℝ)).sqrt (hrad r hr).ne'
    have hl : HasDerivAt (fun x : ℝ => x * t / 32) (t / 32) r := by
      simpa only [one_mul, id_eq] using ((hasDerivAt_id r).mul_const t).div_const 32
    have heq : 2 * r + (-2 * r) / (2 * Real.sqrt (1 - r ^ 2)) + t / 32 =
        D t r := by
      dsimp only [D]
      field_simp [(Real.sqrt_pos.mpr (hrad r hr)).ne']
      ring
    have hh := (hs.add ha).add hl
    rw [heq] at hh
    convert! hh using 1
  have hcontinuous (t : ℝ) : Continuous (U t) :=
    ((continuous_id.pow 2).add
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))).add
      ((continuous_id.mul continuous_const).div_const 32)
  refine ⟨h0lower, h01, h1upper, hsmooth, hderiv, ?_⟩
  intro t ht
  have htAbs : |t| < 3 / 2 := abs_lt.mpr ⟨by linarith only [ht.1], ht.2⟩
  have hpert (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      -3 / 64 < r * t / 32 ∧ r * t / 32 < 3 / 64 := by
    have hh : |r * t| < 3 / 2 := calc
      |r * t| = r * |t| := by rw [abs_mul, abs_of_nonneg hr.1]
      _ ≤ |t| := mul_le_of_le_one_left (abs_nonneg t) hr.2
      _ < 3 / 2 := htAbs
    have hb := abs_lt.mp hh
    constructor <;> linarith only [hb.1, hb.2]
  have hsmall (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (1 / 4)) :
      U t r < 267 / 256 := by
    let a := Real.sqrt (1 - r ^ 2)
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = 1 - r ^ 2 := hradClosed r ⟨hr.1, by linarith [hr.2]⟩
    have haLower : r0 ≤ a := by nlinarith only [h0sq, h0, ha0, ha2, hr.1, hr.2]
    have hprod : 0 ≤ (a - r0) * (a + r0 - 1) :=
      mul_nonneg (sub_nonneg.mpr haLower) (by linarith only [haLower, h0lower])
    have hbase : r ^ 2 + a < 33 / 32 := by
      nlinarith only [ha2, h0sq, hprod, h0fine]
    have hterm : r * t / 32 < 3 / 256 := by
      have hh : |r * t| < 3 / 8 := calc
        |r * t| = r * |t| := by rw [abs_mul, abs_of_nonneg hr.1]
        _ ≤ (1 / 4) * |t| := mul_le_mul_of_nonneg_right hr.2 (abs_nonneg t)
        _ < (1 / 4) * (3 / 2) := mul_lt_mul_of_pos_left htAbs (by norm_num)
        _ = 3 / 8 := by norm_num
      have hrt := (abs_lt.mp hh).2
      linarith only [hrt]
    change r ^ 2 + a + r * t / 32 < _
    linarith only [hbase, hterm]
  have hhalf : (137 / 128 : ℝ) < U t (1 / 2) := by
    have ha0 := Real.sqrt_nonneg (1 - (1 / 2 : ℝ) ^ 2)
    have ha2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ 2)
    have ha : (27 / 32 : ℝ) < Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) := by
      nlinarith only [ha0, ha2]
    dsimp only [U]
    nlinarith only [ha, ht.1]
  have hpositive (r : ℝ) (hr : r ∈ Icc (1 / 4 : ℝ) (3 / 4)) :
      17 / 320 < D t r := by
    let a := Real.sqrt (1 - r ^ 2)
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = 1 - r ^ 2 :=
      hradClosed r ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have ha : (5 / 8 : ℝ) < a := by nlinarith only [ha0, ha2, hr.1, hr.2]
    have haPos : 0 < a := by linarith only [ha]
    have hrPos : 0 < r := by linarith only [hr.1]
    have hdiv : r / a < (8 / 5) * r := (div_lt_iff₀ haPos).mpr (by
      have hp := mul_pos hrPos (sub_pos.mpr ha)
      nlinarith only [hp])
    change 17 / 320 < 2 * r - r / a + t / 32
    nlinarith only [hdiv, hr.1, ht.1]
  have hmono : StrictMonoOn (U t) (Icc (1 / 4 : ℝ) (3 / 4)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hcontinuous t).continuousOn
    intro r hr
    have hr' : r ∈ Icc (1 / 4 : ℝ) (3 / 4) := interior_subset hr
    have hri : r ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
    rw [(hderiv t r hri).deriv]
    linarith only [hpositive r hr']
  have hmiddle (r : ℝ) (hr : r ∈ Icc (3 / 4 : ℝ) r0) :
      73 / 64 < U t r := by
    let a := Real.sqrt (1 - r ^ 2)
    have hr0 : 0 ≤ r := by linarith only [hr.1]
    have hr1 : r ≤ 1 := hr.2.trans h0upper.le
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = 1 - r ^ 2 := hradClosed r ⟨hr0, hr1⟩
    have haLower : (1 / 4 : ℝ) ≤ a := by
      have hsq : r ^ 2 ≤ r0 ^ 2 := pow_le_pow_left₀ hr0 hr.2 2
      nlinarith only [ha0, ha2, hsq, h0sq]
    have haUpper : a < 3 / 4 := by nlinarith only [ha0, ha2, hr.1]
    have hp : 0 ≤ (a - 1 / 4) * (3 / 4 - a) :=
      mul_nonneg (sub_nonneg.mpr haLower) (sub_nonneg.mpr haUpper.le)
    have hbase : (19 / 16 : ℝ) ≤ r ^ 2 + a := by nlinarith only [hp, ha2]
    change 73 / 64 < r ^ 2 + a + r * t / 32
    linarith only [hbase, (hpert r ⟨hr0, hr1⟩).1]
  have hnegative (r : ℝ) (hr : r ∈ Ico r0 (1 : ℝ)) : D t r < -93 / 64 := by
    let a := Real.sqrt (1 - r ^ 2)
    have hr0 : 0 < r := h0.trans_le hr.1
    have hri : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith only [hr0], hr.2⟩
    have haPos : 0 < a := Real.sqrt_pos.mpr (hrad r hri)
    have ha2 : a ^ 2 = 1 - r ^ 2 := hradClosed r ⟨hr0.le, hr.2.le⟩
    have haUpper : a ≤ 1 / 4 := by
      have hsq : r0 ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ h0.le hr.1 2
      nlinarith only [haPos, ha2, hsq, h0sq]
    have hdiv : 4 * r ≤ r / a := (le_div_iff₀ haPos).mpr (by
      have hp := mul_nonneg hr0.le (sub_nonneg.mpr haUpper)
      nlinarith only [hp])
    change 2 * r - r / a + t / 32 < -93 / 64
    linarith only [hdiv, hr.1, h0lower, ht.2]
  have hanti : StrictAntiOn (U t) (Icc r0 (1 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hcontinuous t).continuousOn
    intro r hr
    rw [interior_Icc] at hr
    have hri : r ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith only [hr.1, h0], hr.2⟩
    rw [(hderiv t r hri).deriv]
    linarith only [hnegative r ⟨hr.1.le, hr.2⟩]
  have houter : U t r1 < 4351 / 4096 := by
    have ha0 := Real.sqrt_nonneg (1 - r1 ^ 2)
    have ha2 := hradClosed r1 ⟨h1.le, h1upper.le⟩
    have ha : Real.sqrt (1 - r1 ^ 2) = 1 / 64 := by
      nlinarith only [ha0, ha2, h1sq]
    change r1 ^ 2 + Real.sqrt (1 - r1 ^ 2) + r1 * t / 32 < _
    rw [ha, h1sq]
    linarith only [(hpert r1 ⟨h1.le, h1upper.le⟩).2]
  exact ⟨hsmall, hhalf, hpositive, hmono, hmiddle, hnegative, hanti, houter⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
