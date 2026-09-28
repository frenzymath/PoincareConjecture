import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M09.LocalSmoothInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open Set Metric
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_nestedReference_ordered_morse_chart
    (w : ℝ) (hw_lower : 1 / 2 < w) (hw_upper : w < 3 / 4)
    (hw_root : (2 - 1 / w) * Real.sqrt (1 - w ^ 2) = 1 / 32) :
    ∃ m : OpenPartialHomeomorph E2 (ℝ × ℝ),
      (!₂[-Real.sqrt (1 - w ^ 2), 0] : E2) ∈ m.source ∧
      m.source ⊆ Metric.ball (0 : E2) 1 ∧
      m (!₂[-Real.sqrt (1 - w ^ 2), 0] : E2) = 0 ∧
      ContDiffOn ℝ ∞ m m.source ∧
      ContDiffOn ℝ ∞ m.symm m.target ∧
      ∀ v ∈ m.source,
        ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32 =
          1 - w ^ 2 + w - Real.sqrt (1 - w ^ 2) / 32 -
            (m v).1 ^ 2 + (m v).2 ^ 2 := by
  have hw0 : 0 < w := by linarith
  have hw1 : w < 1 := by linarith
  have hwSq : w ^ 2 < 1 := by
    have h := (sq_lt_sq₀ hw0.le (show (0 : ℝ) ≤ 1 by norm_num)).mpr hw1
    simpa only [one_pow] using h
  let a : ℝ := Real.sqrt (1 - w ^ 2)
  have haSq : a ^ 2 = 1 - w ^ 2 := Real.sq_sqrt (sub_pos.mpr hwSq).le
  have hroot : (1 : ℝ) / 32 = a * (2 - 1 / w) := by
    calc
      (1 : ℝ) / 32 = (2 - 1 / w) * a := hw_root.symm
      _ = a * (2 - 1 / w) := mul_comm _ _
  let p : E2 := !₂[-a, 0]
  have hp0 : p 0 = -a := rfl
  have hp1 : p 1 = 0 := rfl
  have hNorm (v : E2) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  let V : Set E2 := ball 0 1
  have hV : IsOpen V := isOpen_ball
  have hVcoord (v : E2) (hv : v ∈ V) : (v 0) ^ 2 + (v 1) ^ 2 < 1 := by
    have hn : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
    have h := (sq_lt_sq₀ (norm_nonneg v) (show (0 : ℝ) ≤ 1 by norm_num)).mpr hn
    simpa only [one_pow, hNorm v] using h
  have hpV : p ∈ V := by
    apply mem_ball_zero_iff.mpr
    have hnp : ‖p‖ ^ 2 = a ^ 2 := by
      rw [hNorm p, hp0, hp1]
      ring
    nlinarith only [hnp, haSq, pow_pos hw0 2, norm_nonneg p]
  let X : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let Y : E2 →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hX (v : E2) : X v = v 0 := rfl
  have hY (v : E2) : Y v = v 1 := rfl
  have hxSmooth : ContDiff ℝ ∞ (fun v : E2 => v 0) := X.contDiff
  have hySmooth : ContDiff ℝ ∞ (fun v : E2 => v 1) := Y.contDiff
  let r : E2 → ℝ := fun v => Real.sqrt (1 - (v 0) ^ 2)
  let t : E2 → ℝ := fun v => Real.sqrt (1 - (v 0) ^ 2 - (v 1) ^ 2)
  let A : E2 → ℝ := fun v =>
    1 / (r v + w) - 1 - a * (v 0 - a) / (w * (r v + w) ^ 2)
  let B : E2 → ℝ := fun v => 1 - 1 / (t v + r v)
  have hrRad (v : E2) (hv : v ∈ V) : 0 < 1 - (v 0) ^ 2 := by
    nlinarith only [hVcoord v hv, sq_nonneg (v 1)]
  have htRad (v : E2) (hv : v ∈ V) : 0 < 1 - (v 0) ^ 2 - (v 1) ^ 2 := by
    linarith only [hVcoord v hv]
  have hrPos (v : E2) (hv : v ∈ V) : 0 < r v := Real.sqrt_pos.mpr (hrRad v hv)
  have htPos (v : E2) (hv : v ∈ V) : 0 < t v := Real.sqrt_pos.mpr (htRad v hv)
  have hrSq (v : E2) (hv : v ∈ V) : (r v) ^ 2 = 1 - (v 0) ^ 2 :=
    Real.sq_sqrt (hrRad v hv).le
  have htSq (v : E2) (hv : v ∈ V) : (t v) ^ 2 = 1 - (v 0) ^ 2 - (v 1) ^ 2 :=
    Real.sq_sqrt (htRad v hv).le
  have hDpos (v : E2) (hv : v ∈ V) : 0 < r v + w := add_pos (hrPos v hv) hw0
  have hSpos (v : E2) (hv : v ∈ V) : 0 < t v + r v := add_pos (htPos v hv) (hrPos v hv)
  have hrSmooth : ContDiffOn ℝ ∞ r V :=
    (contDiff_const.sub (hxSmooth.pow 2)).contDiffOn.sqrt
      (fun v hv => (hrRad v hv).ne')
  have htSmooth : ContDiffOn ℝ ∞ t V :=
    ((contDiff_const.sub (hxSmooth.pow 2)).sub (hySmooth.pow 2)).contDiffOn.sqrt
      (fun v hv => (htRad v hv).ne')
  have hDSmooth : ContDiffOn ℝ ∞ (fun v : E2 => r v + w) V :=
    hrSmooth.add contDiffOn_const
  have hDsqSmooth : ContDiffOn ℝ ∞ (fun v : E2 => w * (r v + w) ^ 2) V :=
    contDiffOn_const.mul (hDSmooth.pow 2)
  have hNumSmooth : ContDiffOn ℝ ∞ (fun v : E2 => a * (v 0 - a)) V :=
    contDiffOn_const.mul (hxSmooth.contDiffOn.sub contDiffOn_const)
  have hASmooth : ContDiffOn ℝ ∞ A V :=
    ((contDiffOn_const.div hDSmooth (fun v hv => (hDpos v hv).ne')).sub
      contDiffOn_const).sub (hNumSmooth.div hDsqSmooth (fun v hv =>
        mul_ne_zero hw0.ne' (pow_ne_zero 2 (hDpos v hv).ne')))
  have hBSmooth : ContDiffOn ℝ ∞ B V :=
    contDiffOn_const.sub (contDiffOn_const.div (htSmooth.add hrSmooth)
      (fun v hv => (hSpos v hv).ne'))
  have hrp : r p = w := by
    change Real.sqrt (1 - (-a) ^ 2) = w
    have h : 1 - (-a) ^ 2 = w ^ 2 := by nlinarith only [haSq]
    rw [h, Real.sqrt_sq_eq_abs, abs_of_pos hw0]
  have htp : t p = w := by
    change Real.sqrt (1 - (-a) ^ 2 - (0 : ℝ) ^ 2) = w
    have h : 1 - (-a) ^ 2 - (0 : ℝ) ^ 2 = w ^ 2 := by nlinarith only [haSq]
    rw [h, Real.sqrt_sq_eq_abs, abs_of_pos hw0]
  have hAp : A p = 1 / (2 * w ^ 3) - 1 := by
    calc
      A p = (a ^ 2 + w ^ 2) / (2 * w ^ 3) - 1 := by
        change 1 / (r p + w) - 1 - a * (p 0 - a) / (w * (r p + w) ^ 2) = _
        rw [hrp, hp0, show w + w = 2 * w by ring]
        field_simp [hw0.ne']
        ring
      _ = 1 / (2 * w ^ 3) - 1 := by
        rw [show a ^ 2 + w ^ 2 = 1 by linarith only [haSq]]
  have hBp : B p = 1 - 1 / (2 * w) := by
    change 1 - 1 / (t p + r p) = _
    rw [htp, hrp, show w + w = 2 * w by ring]
  have hwSqSmall : w ^ 2 < ((3 : ℝ) / 4) ^ 2 :=
    (sq_lt_sq₀ hw0.le (by norm_num)).mpr hw_upper
  have hwCubeSmall : w ^ 3 < 27 / 64 := by
    have h1 := mul_lt_mul_of_pos_left hwSqSmall hw0
    have h2 := mul_lt_mul_of_pos_right hw_upper
      (by norm_num : (0 : ℝ) < ((3 : ℝ) / 4) ^ 2)
    nlinarith only [h1, h2]
  have hApos : 0 < A p := by
    rw [hAp]
    exact sub_pos.mpr (one_lt_one_div
      (mul_pos (by norm_num) (pow_pos hw0 3)) (by linarith only [hwCubeSmall]))
  have hBpos : 0 < B p := by
    rw [hBp]
    apply sub_pos.mpr
    apply (div_lt_iff₀ (show (0 : ℝ) < 2 * w by positivity)).mpr
    linarith only [hw_lower]
  have hfactor (v : E2) (hv : v ∈ V) :
      (v 0) ^ 2 + (v 1) ^ 2 + t v + v 0 / 32 - (a ^ 2 + w - a / 32) =
        -A v * (v 0 + a) ^ 2 + B v * (v 1) ^ 2 := by
    have hD : r v + w ≠ 0 := (hDpos v hv).ne'
    have hS : t v + r v ≠ 0 := (hSpos v hv).ne'
    have htr : t v - r v = -(v 1) ^ 2 / (t v + r v) := by
      apply (eq_div_iff hS).mpr
      nlinarith only [htSq v hv, hrSq v hv]
    have hrw : r v - w = -(v 0 + a) * (v 0 - a) / (r v + w) := by
      apply (eq_div_iff hD).mpr
      nlinarith only [hrSq v hv, haSq]
    have hwr : w - r v = (v 0 + a) * (v 0 - a) / (r v + w) := by
      apply (eq_div_iff hD).mpr
      nlinarith only [hrSq v hv, haSq]
    have hlinear : (v 0 + a) / 32 = (v 0 + a) * (a * (2 - 1 / w)) := by
      calc
        (v 0 + a) / 32 = (v 0 + a) * ((1 : ℝ) / 32) := by ring
        _ = (v 0 + a) * (a * (2 - 1 / w)) := by rw [hroot]
    have hphi :
        (v 0) ^ 2 + r v + v 0 / 32 - (a ^ 2 + w - a / 32) =
          (v 0 + a) * ((v 0 - a) * (1 - 1 / (r v + w)) + a * (2 - 1 / w)) := by
      calc
        (v 0) ^ 2 + r v + v 0 / 32 - (a ^ 2 + w - a / 32) =
            (v 0 + a) * (v 0 - a) + (r v - w) + (v 0 + a) / 32 := by ring
        _ = (v 0 + a) *
            ((v 0 - a) * (1 - 1 / (r v + w)) + a * (2 - 1 / w)) := by
          rw [hrw, hlinear]
          ring
    have hbracket :
        (v 0 - a) * (1 - 1 / (r v + w)) + a * (2 - 1 / w) =
          (v 0 + a) * (1 - 1 / (r v + w)) + a * (w - r v) / (w * (r v + w)) := by
      field_simp [hw0.ne', hD]
      ring
    have hphiFactor :
        (v 0) ^ 2 + r v + v 0 / 32 - (a ^ 2 + w - a / 32) =
          -A v * (v 0 + a) ^ 2 := by
      rw [hphi, hbracket, hwr]
      change (v 0 + a) * ((v 0 + a) * (1 - 1 / (r v + w)) +
          a * ((v 0 + a) * (v 0 - a) / (r v + w)) / (w * (r v + w))) =
        -(1 / (r v + w) - 1 - a * (v 0 - a) / (w * (r v + w) ^ 2)) *
          (v 0 + a) ^ 2
      field_simp [hw0.ne', hD]
      ring
    calc
      (v 0) ^ 2 + (v 1) ^ 2 + t v + v 0 / 32 - (a ^ 2 + w - a / 32) =
          ((v 0) ^ 2 + r v + v 0 / 32 - (a ^ 2 + w - a / 32)) +
            (v 1) ^ 2 + (t v - r v) := by ring
      _ = -A v * (v 0 + a) ^ 2 + B v * (v 1) ^ 2 := by
        rw [hphiFactor, htr]
        change -A v * (v 0 + a) ^ 2 + (v 1) ^ 2 + (-(v 1) ^ 2 / (t v + r v)) =
          -A v * (v 0 + a) ^ 2 + (1 - 1 / (t v + r v)) * (v 1) ^ 2
        ring
  let W : Set E2 := V ∩ {v | 0 < A v}
  have hW : IsOpen W := hASmooth.continuousOn.isOpen_inter_preimage hV isOpen_Ioi
  let U : Set E2 := W ∩ {v | 0 < B v}
  have hU : IsOpen U :=
    (hBSmooth.continuousOn.mono (show W ⊆ V from inter_subset_left)).isOpen_inter_preimage
      hW isOpen_Ioi
  have hUV : U ⊆ V := fun _ hv => hv.1.1
  have hpU : p ∈ U := ⟨⟨hpV, hApos⟩, hBpos⟩
  have hASqrt : ContDiffOn ℝ ∞ (fun v : E2 => Real.sqrt (A v)) U :=
    (hASmooth.mono hUV).sqrt (fun _ hv => ne_of_gt hv.1.2)
  have hBSqrt : ContDiffOn ℝ ∞ (fun v : E2 => Real.sqrt (B v)) U :=
    (hBSmooth.mono hUV).sqrt (fun _ hv => ne_of_gt hv.2)
  let g : E2 → ℝ × ℝ := fun v =>
    (Real.sqrt (A v) * (v 0 + a), Real.sqrt (B v) * v 1)
  have hg : ContDiffOn ℝ ∞ g U :=
    (hASqrt.mul (hxSmooth.contDiffOn.add contDiffOn_const)).prodMk
      (hBSqrt.mul hySmooth.contDiffOn)
  have hgp : g p = 0 := by
    apply Prod.ext
    · change Real.sqrt (A p) * (p 0 + a) = 0
      rw [hp0, neg_add_cancel, mul_zero]
    · change Real.sqrt (B p) * p 1 = 0
      rw [hp1, mul_zero]
  let alpha : ℝ := Real.sqrt (A p)
  let beta : ℝ := Real.sqrt (B p)
  have halpha : 0 < alpha := Real.sqrt_pos.mpr hApos
  have hbeta : 0 < beta := Real.sqrt_pos.mpr hBpos
  let L : E2 →L[ℝ] (ℝ × ℝ) := (alpha • X).prod (beta • Y)
  have hL (v : E2) : L v = (alpha * v 0, beta * v 1) := rfl
  have hdx : HasFDerivAt (fun v : E2 => v 0 + a) X p := by
    simpa only [hX] using (X.hasFDerivAt (x := p)).add_const a
  have hdy : HasFDerivAt (fun v : E2 => v 1) Y p := by
    change HasFDerivAt (Y : E2 → ℝ) Y p
    exact Y.hasFDerivAt
  have hleft : HasFDerivAt (fun v : E2 => Real.sqrt (A v) * (v 0 + a))
      (alpha • X) p := by
    have h := (((hASqrt.contDiffAt (hU.mem_nhds hpU)).differentiableAt
      (by simp)).hasFDerivAt).mul hdx
    change HasFDerivAt (fun v : E2 => Real.sqrt (A v) * (v 0 + a)) _ p at h
    simpa only [alpha, hp0, neg_add_cancel, zero_smul, add_zero] using h
  have hright : HasFDerivAt (fun v : E2 => Real.sqrt (B v) * v 1)
      (beta • Y) p := by
    have h := (((hBSqrt.contDiffAt (hU.mem_nhds hpU)).differentiableAt
      (by simp)).hasFDerivAt).mul hdy
    change HasFDerivAt (fun v : E2 => Real.sqrt (B v) * v 1) _ p at h
    simpa only [beta, hp1, zero_smul, add_zero] using h
  have hdg : HasFDerivAt g L p := hleft.prodMk hright
  have hdf : fderiv ℝ g p = L := hdg.fderiv
  have hLi : Function.Injective L := by
    intro v z hvz
    have hx : alpha * v 0 = alpha * z 0 := by
      simpa only [hL] using congrArg Prod.fst hvz
    have hy : beta * v 1 = beta * z 1 := by
      simpa only [hL] using congrArg Prod.snd hvz
    have hx' : v 0 = z 0 := mul_left_cancel₀ halpha.ne' hx
    have hy' : v 1 = z 1 := mul_left_cancel₀ hbeta.ne' hy
    ext i
    fin_cases i
    · exact hx'
    · exact hy'
  have hLs : Function.Surjective L := by
    rintro ⟨s, z⟩
    refine ⟨(!₂[s / alpha, z / beta] : E2), ?_⟩
    rw [hL]
    apply Prod.ext
    · change alpha * (s / alpha) = s
      field_simp [halpha.ne']
    · change beta * (z / beta) = z
      field_simp [hbeta.ne']
  have hbij : Function.Bijective (fderiv ℝ g p) := by
    rw [hdf]
    exact ⟨hLi, hLs⟩
  obtain ⟨m, hpm, hmU, hmg, hmi, _hmbij⟩ :=
    PoincareConjecture.Proofs.M09.exists_smooth_local_inverse g U hU hg p hpU hbij
  refine ⟨m, hpm, hmU.trans hUV, ?_, ?_, hmi, ?_⟩
  · rw [hmg]
    exact hgp
  · rw [hmg]
    exact hg.mono hmU
  · intro v hv
    have hvU : v ∈ U := hmU hv
    have hvV : v ∈ V := hUV hvU
    have hA0 : 0 < A v := hvU.1.2
    have hB0 : 0 < B v := hvU.2
    have hfirst : (g v).1 ^ 2 = A v * (v 0 + a) ^ 2 := by
      change (Real.sqrt (A v) * (v 0 + a)) ^ 2 = _
      rw [mul_pow, Real.sq_sqrt hA0.le]
    have hsecond : (g v).2 ^ 2 = B v * (v 1) ^ 2 := by
      change (Real.sqrt (B v) * v 1) ^ 2 = _
      rw [mul_pow, Real.sq_sqrt hB0.le]
    have htNorm : Real.sqrt (1 - ‖v‖ ^ 2) = t v := by
      rw [hNorm v]
      change Real.sqrt (1 - ((v 0) ^ 2 + (v 1) ^ 2)) =
        Real.sqrt (1 - (v 0) ^ 2 - (v 1) ^ 2)
      apply congrArg Real.sqrt
      ring
    rw [hmg, htNorm, hNorm v, hfirst, hsecond]
    change (v 0) ^ 2 + (v 1) ^ 2 + t v + v 0 / 32 =
      1 - w ^ 2 + w - a / 32 - A v * (v 0 + a) ^ 2 + B v * (v 1) ^ 2
    nlinarith only [hfactor v hvV, haSq]

end PoincareConjecture.M25.Topology3D
