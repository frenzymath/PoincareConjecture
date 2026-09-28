import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceMeridian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem nonnested_reference_exterior_scalar_bounds
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (a : ℝ) (ha : 0 < a) (haCorrection : 16 / sigma < a ^ 2)
    (haLarge : 8 < a ^ 2) :
    let L : OpenPartialHomeomorph ℝ ℝ := Classical.choose
      (Classical.choose_spec (Classical.choose_spec
        (exists_nonnested_reference_meridian sigma hsigma hsigmaSmall
          d hd hdNear hdZero hdBounds hdDeriv)))
    let b : ℝ := 1 / (128 * a ^ 2)
    let H : Set ℝ := Icc (-4 * b) (4 * b)
    let D : Set ℝ := Icc (1 / 4 : ℝ) (9 / 8)
    let r : ℝ → ℝ := fun h => Real.sqrt (1 / 4 + h)
    let theta : ℝ → ℝ → ℝ := fun h R =>
      Real.arccos (Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h)
    let K : ℝ → ℝ := fun w => w ^ 2 + w + d (1 - w ^ 2)
    let S : ℝ → ℝ := fun w => 1 + w + d (1 - w ^ 2)
    let wR : ℝ → ℝ := fun R => -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)
    (∀ h ∈ H, 0 < r h ∧ (r h) ^ 2 = 1 / 4 + h ∧ r h < 3 / 4 ∧
      ContDiffAt ℝ ∞ r h) ∧
    (∀ R ∈ D,
      (0 < R ^ 2 / a ^ 2 ∧ R ^ 2 / a ^ 2 < 1 / 4 ∧
        2 * R ^ 2 / a ^ 2 < sigma / 2 ∧ 1 / (16 * a ^ 2) ≤ R ^ 2 / a ^ 2) ∧
      (-1 < wR R ∧ wR R < -3 / 4 ∧ wR R ∈ L.source ∧
        S (wR R) = R ^ 2 / a ^ 2 ∧ K (wR R) = -R ^ 2 / a ^ 2 ∧
        L (wR R) = -Real.sqrt (1 / 4 - R ^ 2 / a ^ 2)) ∧
      (∀ h ∈ H, 0 < theta h R ∧ theta h R < Real.pi / 2 ∧
        Real.cos (theta h R) = Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h ∧
        ContDiffAt ℝ ∞ (fun s => theta s R) h)) ∧
    (∀ h ∈ H, StrictMonoOn (theta h) D) ∧
    StrictMonoOn S (Icc (-1 : ℝ) (1 / 4)) ∧
    (∀ (R w : ℝ), R ∈ D → w ∈ Ioo (-1 : ℝ) (1 / 4) →
      (2 * R ^ 2 / a ^ 2 ≤ 1 - w ^ 2 ↔ wR R ≤ w) ∧
      (2 * R ^ 2 / a ^ 2 < 1 - w ^ 2 ↔ wR R < w)) := by
  classical
  let H := exists_nonnested_reference_meridian sigma hsigma hsigmaSmall
    d hd hdNear hdZero hdBounds hdDeriv
  let L : OpenPartialHomeomorph ℝ ℝ := Classical.choose
    (Classical.choose_spec (Classical.choose_spec H))
  obtain ⟨he, heSmall, hell, hLs, hLt, hLc, hLi, hLm, hLd, hLf,
    hLe, hLminus, hLhalf, hLzero, hLaff, hLsq⟩ :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H))
  let b : ℝ := 1 / (128 * a ^ 2)
  let Ht : Set ℝ := Icc (-4 * b) (4 * b)
  let Rt : Set ℝ := Icc (1 / 4 : ℝ) (9 / 8)
  let r : ℝ → ℝ := fun h => Real.sqrt (1 / 4 + h)
  let theta : ℝ → ℝ → ℝ := fun h R =>
    Real.arccos (Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h)
  let K : ℝ → ℝ := fun w => w ^ 2 + w + d (1 - w ^ 2)
  let S : ℝ → ℝ := fun w => 1 + w + d (1 - w ^ 2)
  let wR : ℝ → ℝ := fun R => -Real.sqrt (1 - 2 * R ^ 2 / a ^ 2)
  let v : ℝ := 1 / a ^ 2
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hv : 0 < v := by dsimp [v]; positivity
  have hv8 : v < 1 / 8 := by dsimp [v]; rw [div_lt_iff₀ ha2]; linarith
  have hvSigma : v < sigma / 16 := by
    have hh := (div_lt_iff₀ hsigma).mp haCorrection
    dsimp [v]
    rw [div_lt_iff₀ ha2]
    nlinarith
  have hdiv (x : ℝ) : x / a ^ 2 = x * v := by dsimp [v]; ring
  have hb4 : 4 * b = v / 32 := by dsimp [b, v]; ring
  have hr (h : ℝ) (hh : h ∈ Ht) :
      0 < r h ∧ (r h) ^ 2 = 1 / 4 + h ∧ r h < 3 / 4 := by
    have hlo := hh.1
    have hhi := hh.2
    rw [neg_mul, hb4] at hlo
    rw [hb4] at hhi
    have hp : 0 < 1 / 4 + h := by linarith only [hlo, hv8]
    have hs : (r h) ^ 2 = 1 / 4 + h := Real.sq_sqrt hp.le
    exact ⟨Real.sqrt_pos.mpr hp, hs, by nlinarith only [hs, hhi, hv8]⟩
  have hscale (R : ℝ) (hR : R ∈ Rt) :
      0 < R ^ 2 / a ^ 2 ∧ R ^ 2 / a ^ 2 < 1 / 4 ∧
      2 * R ^ 2 / a ^ 2 < sigma / 2 ∧ v / 16 ≤ R ^ 2 / a ^ 2 := by
    have hRlo : 1 / 16 ≤ R ^ 2 := by nlinarith only [hR.1, sq_nonneg (R - 1 / 4)]
    have hRhi : R ^ 2 ≤ 81 / 64 := by
      nlinarith only [(sq_le_sq₀ (by linarith only [hR.1])
        (by norm_num : (0 : ℝ) ≤ 9 / 8)).mpr hR.2]
    have hl := mul_le_mul_of_nonneg_right hRlo hv.le
    have hu := mul_le_mul_of_nonneg_right hRhi hv.le
    simp only [hdiv]
    refine ⟨mul_pos (by linarith only [hRlo]) hv, ?_, ?_, ?_⟩ <;>
      nlinarith only [hl, hu, hv8, hvSigma]
  have htheta (h R : ℝ) (hh : h ∈ Ht) (hR : R ∈ Rt) :
      0 < theta h R ∧ theta h R < Real.pi / 2 ∧
      Real.cos (theta h R) = Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h := by
    have hs := hscale R hR
    have hrh := hr h hh
    have hp : 0 < 1 / 4 - R ^ 2 / a ^ 2 := by linarith only [hs.2.1]
    have hsq := Real.sq_sqrt hp.le
    have hpos : 0 < Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h :=
      div_pos (Real.sqrt_pos.mpr hp) hrh.1
    have hlt : Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h < 1 := by
      rw [div_lt_one hrh.1]
      have hlo := hh.1
      rw [neg_mul, hb4] at hlo
      nlinarith only [hsq, hrh.1, hrh.2.1, hlo, hs.2.2.2, hv]
    exact ⟨Real.arccos_pos.mpr hlt, Real.arccos_lt_pi_div_two.mpr hpos,
      Real.cos_arccos (by linarith only [hpos]) hlt.le⟩
  have hrd (h : ℝ) (hh : h ∈ Ht) : ContDiffAt ℝ ∞ r h :=
    (contDiffAt_const.add contDiffAt_id).sqrt (by
      change 1 / 4 + h ≠ 0
      have hh' := hr h hh
      nlinarith only [hh'.2.1, sq_pos_of_pos hh'.1])
  have htd (R : ℝ) (hR : R ∈ Rt) (h : ℝ) (hh : h ∈ Ht) :
      ContDiffAt ℝ ∞ (fun s => theta s R) h := by
    have hrh := hr h hh
    have hs := hscale R hR
    have hp : 0 < Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h :=
      div_pos (Real.sqrt_pos.mpr (by linarith only [hs.2.1])) hrh.1
    have hl : Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) / r h < 1 :=
      Real.arccos_pos.mp (htheta h R hh hR).1
    exact (Real.contDiffAt_arccos (by linarith only [hp]) (by linarith only [hl])).comp h
      (contDiffAt_const.div (hrd h hh) hrh.1.ne')
  have hwR (R : ℝ) (hR : R ∈ Rt) :
      -1 < wR R ∧ wR R < -3 / 4 ∧ wR R ∈ L.source ∧
      S (wR R) = R ^ 2 / a ^ 2 ∧ K (wR R) = -R ^ 2 / a ^ 2 ∧
      L (wR R) = -Real.sqrt (1 / 4 - R ^ 2 / a ^ 2) := by
    have hs := hscale R hR
    have hq : 0 ≤ 2 * R ^ 2 / a ^ 2 := by positivity
    have hqsmall : 2 * R ^ 2 / a ^ 2 < 1 / 32 :=
      by linarith only [hs.2.2.1, hsigmaSmall]
    have hsq : (wR R) ^ 2 = 1 - 2 * R ^ 2 / a ^ 2 := by
      dsimp only [wR]
      rw [neg_sq, Real.sq_sqrt (by linarith only [hqsmall])]
    have hqpos : 0 < 2 * R ^ 2 / a ^ 2 := by
      rw [mul_div_assoc]
      exact mul_pos (by norm_num) hs.1
    have hlo : -1 < wR R := neg_lt_neg ((Real.sqrt_lt' zero_lt_one).mpr
      (by nlinarith only [hqpos]))
    have hhi : wR R < -3 / 4 := by
      have hh : (3 / 4 : ℝ) < Real.sqrt (1 - 2 * R ^ 2 / a ^ 2) :=
        (Real.lt_sqrt (by norm_num)).mpr (by linarith only [hqsmall])
      simpa only [wR, neg_div] using neg_lt_neg hh
    have hmem : wR R ∈ L.source := by
      rw [hLs]
      exact ⟨by linarith only [he, hlo], by linarith only [hhi]⟩
    have heq : 1 - (wR R) ^ 2 = 2 * R ^ 2 / a ^ 2 := by linarith only [hsq]
    have hdq := hdNear _ hq hs.2.2.1.le
    have hdw : d (1 - (wR R) ^ 2) = -(wR R) - 1 + R ^ 2 / a ^ 2 := by
      rw [heq, hdq]
      dsimp only [wR]
      ring
    have hS : S (wR R) = R ^ 2 / a ^ 2 := by dsimp [S]; rw [hdw]; ring
    have hK : K (wR R) = -R ^ 2 / a ^ 2 := by
      dsimp [K]
      rw [hdw, hsq]
      ring
    refine ⟨hlo, hhi, hmem, hS, hK, ?_⟩
    rw [hLf, if_pos (by linarith only [hhi])]
    change -Real.sqrt (K (wR R) + 1 / 4) = _
    rw [hK]
    congr 2
    ring
  have hS : ContDiff ℝ ∞ S := (contDiff_const.add contDiff_id).add
    (hd.comp (contDiff_const.sub (contDiff_id.pow 2)))
  have hSmono : StrictMonoOn S (Icc (-1 : ℝ) (1 / 4)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hS.continuous.continuousOn
    intro w hw
    have hi : w ∈ Icc (-1 : ℝ) (1 / 4) := interior_subset hw
    have hq0 : 0 ≤ 1 - w ^ 2 := by
      nlinarith only [mul_nonneg (by linarith only [hi.1] : 0 ≤ w + 1)
        (by linarith only [hi.2] : 0 ≤ 1 - w)]
    have haW : |w| ≤ 1 := abs_le.mpr ⟨hi.1, by linarith [hi.2]⟩
    have hp : HasDerivAt (fun z : ℝ => z ^ 2) (2 * w) w :=
      by simpa using hasDerivAt_pow 2 w
    have hh := ((hd.differentiable (by simp) (1 - w ^ 2)).hasDerivAt).comp w
      (hp.const_sub 1)
    have hdS : HasDerivAt S (1 - 2 * w * deriv d (1 - w ^ 2)) w :=
      (((hasDerivAt_id w).const_add 1).add hh).congr_deriv (by ring)
    rw [hdS.deriv]
    have hab := hdDeriv (1 - w ^ 2) hq0
    have hbnd : |2 * w * deriv d (1 - w ^ 2)| ≤ 1 / 8 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        2 * |w| * |deriv d (1 - w ^ 2)| ≤ 2 * 1 * (1 / 16) :=
          mul_le_mul (mul_le_mul_of_nonneg_left haW (by norm_num)) hab
            (abs_nonneg _) (by norm_num)
        _ = 1 / 8 := by ring
    linarith only [(abs_le.mp hbnd).2]
  have hqCompare (R w : ℝ) (hR : R ∈ Rt) (hw : w ∈ Ioo (-1 : ℝ) (1 / 4)) :
      (2 * R ^ 2 / a ^ 2 ≤ 1 - w ^ 2 ↔ wR R ≤ w) ∧
      (2 * R ^ 2 / a ^ 2 < 1 - w ^ 2 ↔ wR R < w) := by
    have hs := hscale R hR
    have hwr := hwR R hR
    have hp : 0 ≤ 1 - 2 * R ^ 2 / a ^ 2 := by linarith only [hs.2.2.1, hsigmaSmall]
    have hsq : (wR R) ^ 2 = 1 - 2 * R ^ 2 / a ^ 2 := by
      dsimp only [wR]; rw [neg_sq, Real.sq_sqrt hp]
    by_cases hn : w ≤ 0
    · have hle := sq_le_sq₀ (neg_nonneg.mpr hn)
        (neg_nonneg.mpr (by linarith only [hwr.2.1] : wR R ≤ 0))
      have hlt := sq_lt_sq₀ (neg_nonneg.mpr hn)
        (neg_nonneg.mpr (by linarith only [hwr.2.1] : wR R ≤ 0))
      rw [neg_sq, neg_sq, hsq] at hle hlt
      constructor
      · constructor
        · intro h; have hh := hle.mp (by linarith only [h]); linarith only [hh]
        · intro h; have hh := hle.mpr (by linarith only [h]); linarith only [hh]
      · constructor
        · intro h; have hh := hlt.mp (by linarith only [h]); linarith only [hh]
        · intro h; have hh := hlt.mpr (by linarith only [h]); linarith only [hh]
    · have hq : 2 * R ^ 2 / a ^ 2 < 1 - w ^ 2 := by
        have hw2 : w ^ 2 < (1 / 4 : ℝ) ^ 2 :=
          (sq_lt_sq₀ (by linarith only [hn]) (by norm_num)).mpr hw.2
        nlinarith only [hs.2.2.1, hsigmaSmall, hw2]
      have hl : wR R < w := by linarith only [hwr.2.1, hn]
      exact ⟨iff_of_true hq.le hl.le, iff_of_true hq hl⟩
  refine ⟨fun h hh => ⟨(hr h hh).1, (hr h hh).2.1, (hr h hh).2.2, hrd h hh⟩,
    ?_, ?_, hSmono, hqCompare⟩
  · intro R hR
    refine ⟨?_, hwR R hR, fun h hh =>
      ⟨(htheta h R hh hR).1, (htheta h R hh hR).2.1,
        (htheta h R hh hR).2.2, htd R hR h hh⟩⟩
    have hl : 1 / (16 * a ^ 2) = v / 16 := by dsimp [v]; ring
    exact ⟨(hscale R hR).1, (hscale R hR).2.1, (hscale R hR).2.2.1,
      hl ▸ (hscale R hR).2.2.2⟩
  · intro h hh R₁ hR₁ R₂ hR₂ hlt
    have hsq : R₁ ^ 2 < R₂ ^ 2 :=
      (sq_lt_sq₀ (by linarith only [hR₁.1]) (by linarith only [hR₂.1])).mpr hlt
    have hdivlt := div_lt_div_of_pos_right hsq ha2
    have hroot : Real.sqrt (1 / 4 - R₂ ^ 2 / a ^ 2) <
        Real.sqrt (1 / 4 - R₁ ^ 2 / a ^ 2) :=
      Real.sqrt_lt_sqrt (by linarith only [(hscale R₂ hR₂).2.1])
        (by linarith only [hdivlt])
    have harg := div_lt_div_of_pos_right hroot (hr h hh).1
    exact Real.arccos_lt_arccos
      (by have hp := Real.arccos_lt_pi_div_two.mp (htheta h R₂ hh hR₂).2.1
          linarith only [hp]) harg (Real.arccos_pos.mp (htheta h R₁ hh hR₁).1).le

end PoincareConjecture.M25.Topology3D
