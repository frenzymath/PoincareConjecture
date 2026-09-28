import PoincareConjecture.Proofs.M03.Existence.QuasilinearDeTurckNative
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace PoincareConjecture.QuasilinearDeTurckNative

open SpectralHeatNative

variable {iota : Type*} [Countable iota]

def traceScale (lambda : iota → NNReal) (r : ℝ) (x : State iota) : ℝ :=
  r / max r ‖shiftedBaseMultiplier lambda x‖

def traceCutoff (lambda : iota → NNReal) (r : ℝ) (x : State iota) : State iota :=
  traceScale lambda r x • x

theorem traceScale_nonneg (lambda : iota → NNReal) {r : ℝ} (hr : 0 < r)
    (x : State iota) : 0 ≤ traceScale lambda r x :=
  div_nonneg hr.le (hr.le.trans (le_max_left _ _))

theorem traceScale_le_one (lambda : iota → NNReal) {r : ℝ} (hr : 0 < r)
    (x : State iota) : traceScale lambda r x ≤ 1 := by
  exact (div_le_one (hr.trans_le (le_max_left _ _))).mpr (le_max_left _ _)

theorem continuous_traceCutoff (lambda : iota → NNReal) {r : ℝ} (hr : 0 < r) :
    Continuous (traceCutoff lambda r) := by
  have hd : ∀ x : State iota, max r ‖shiftedBaseMultiplier lambda x‖ ≠ 0 :=
    fun x => (hr.trans_le (le_max_left _ _)).ne'
  exact (continuous_const.div
    (continuous_const.max (shiftedBaseMultiplier lambda).continuous.norm) hd).smul
      continuous_id

@[simp] theorem traceCutoff_eq_self (lambda : iota → NNReal) {r : ℝ}
    (hr : 0 < r) {x : State iota} (hx : ‖shiftedBaseMultiplier lambda x‖ ≤ r) :
    traceCutoff lambda r x = x := by
  simp only [traceCutoff, traceScale, max_eq_left hx, div_self hr.ne', one_smul]

@[simp] theorem traceCutoff_zero (lambda : iota → NNReal) (r : ℝ) :
    traceCutoff lambda r 0 = 0 := by simp [traceCutoff]

theorem norm_traceCutoff_le (lambda : iota → NNReal) {r : ℝ} (hr : 0 < r)
    (x : State iota) : ‖traceCutoff lambda r x‖ ≤ ‖x‖ := by
  rw [traceCutoff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (traceScale_nonneg lambda hr x)]
  exact (mul_le_mul_of_nonneg_right (traceScale_le_one lambda hr x) (norm_nonneg x)).trans_eq
    (one_mul _)

theorem norm_trace_traceCutoff_le (lambda : iota → NNReal) {r : ℝ} (hr : 0 < r)
    (x : State iota) :
    ‖shiftedBaseMultiplier lambda (traceCutoff lambda r x)‖ ≤ r := by
  rw [traceCutoff, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (traceScale_nonneg lambda hr x)]
  calc
    _ ≤ traceScale lambda r x * max r ‖shiftedBaseMultiplier lambda x‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (traceScale_nonneg lambda hr x)
    _ = r := div_mul_cancel₀ _ (hr.trans_le (le_max_left _ _)).ne'

theorem norm_trace_traceCutoff_le_original (lambda : iota → NNReal)
    {r : ℝ} (hr : 0 < r) (x : State iota) :
    ‖shiftedBaseMultiplier lambda (traceCutoff lambda r x)‖ ≤
      ‖shiftedBaseMultiplier lambda x‖ := by
  rw [traceCutoff, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (traceScale_nonneg lambda hr x)]
  exact (mul_le_mul_of_nonneg_right (traceScale_le_one lambda hr x)
    (norm_nonneg _)).trans_eq (one_mul _)

private theorem scalar_scale_difference {r : ℝ} (hr : 0 < r) (t s : ℝ) :
    max r s * |r / max r t - r / max r s| ≤ |t - s| := by
  let a := max r t
  let b := max r s
  have ha : 0 < a := hr.trans_le (le_max_left _ _)
  have hb : 0 < b := hr.trans_le (le_max_left _ _)
  have hc : 0 ≤ r / a := div_nonneg hr.le ha.le
  have hc1 : r / a ≤ 1 := (div_le_one ha).mpr (le_max_left _ _)
  have hm : |b - a| ≤ |t - s| := by
    change |max r s - max r t| ≤ |t - s|
    calc
      _ ≤ max |r - r| |s - t| := abs_max_sub_max_le_max r s r t
      _ = |t - s| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg (s - t)), abs_sub_comm]
  have heq : r / a - r / b = (r / a) * (b - a) / b := by
    field_simp [ha.ne', hb.ne']
    <;> ring
  change b * |r / a - r / b| ≤ _
  rw [heq, abs_div, abs_mul, abs_of_nonneg hc, abs_of_pos hb]
  calc
    _ = (r / a) * |b - a| := by field_simp [hb.ne']
    _ ≤ |b - a| := (mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)).trans_eq (one_mul _)
    _ ≤ |t - s| := hm

theorem traceScale_difference_weighted (lambda : iota → NNReal) {r : ℝ}
    (hr : 0 < r) (x y : State iota) :
    max r ‖shiftedBaseMultiplier lambda y‖ *
        |traceScale lambda r x - traceScale lambda r y| ≤
      ‖shiftedBaseMultiplier lambda (x - y)‖ := by
  apply (scalar_scale_difference hr _ _).trans
  simpa only [map_sub] using abs_norm_sub_norm_le
    (shiftedBaseMultiplier lambda x) (shiftedBaseMultiplier lambda y)

private theorem traceCutoff_sub (lambda : iota → NNReal) (r : ℝ) (x y : State iota) :
    traceCutoff lambda r x - traceCutoff lambda r y =
      traceScale lambda r x • (x - y) +
        (traceScale lambda r x - traceScale lambda r y) • y := by
  simp only [traceCutoff, smul_sub, sub_smul]
  abel

theorem norm_traceCutoff_sub_le (lambda : iota → NNReal) {r : ℝ} (hr : 0 < r)
    (x y : State iota) :
    ‖traceCutoff lambda r x - traceCutoff lambda r y‖ ≤
      ‖x - y‖ + |traceScale lambda r x - traceScale lambda r y| * ‖y‖ := by
  rw [traceCutoff_sub]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (traceScale_nonneg lambda hr x)]
  exact add_le_add
    ((mul_le_mul_of_nonneg_right (traceScale_le_one lambda hr x)
      (norm_nonneg (x - y))).trans_eq (one_mul _)) le_rfl

theorem norm_trace_traceCutoff_sub_le (lambda : iota → NNReal) {r : ℝ}
    (hr : 0 < r) (x y : State iota) :
    ‖shiftedBaseMultiplier lambda (traceCutoff lambda r x - traceCutoff lambda r y)‖ ≤
      2 * ‖shiftedBaseMultiplier lambda (x - y)‖ := by
  have hw : |traceScale lambda r x - traceScale lambda r y| *
      ‖shiftedBaseMultiplier lambda y‖ ≤ ‖shiftedBaseMultiplier lambda (x - y)‖ := by
    calc
      _ = ‖shiftedBaseMultiplier lambda y‖ *
          |traceScale lambda r x - traceScale lambda r y| := mul_comm _ _
      _ ≤ max r ‖shiftedBaseMultiplier lambda y‖ *
          |traceScale lambda r x - traceScale lambda r y| :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
      _ ≤ _ := traceScale_difference_weighted lambda hr x y
  rw [traceCutoff_sub, map_add, map_smul, map_smul]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (traceScale_nonneg lambda hr x)]
  have hx := mul_le_mul_of_nonneg_right (traceScale_le_one lambda hr x)
    (norm_nonneg (shiftedBaseMultiplier lambda (x - y)))
  nlinarith

theorem weighted_norm_traceCutoff_sub_le (lambda : iota → NNReal) {r : ℝ}
    (hr : 0 < r) (x y : State iota) :
    max ‖shiftedBaseMultiplier lambda (traceCutoff lambda r x)‖
        ‖shiftedBaseMultiplier lambda (traceCutoff lambda r y)‖ *
      ‖traceCutoff lambda r x - traceCutoff lambda r y‖ ≤
        max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ * ‖x - y‖ +
          ‖shiftedBaseMultiplier lambda (x - y)‖ * ‖y‖ := by
  let m := max ‖shiftedBaseMultiplier lambda (traceCutoff lambda r x)‖
    ‖shiftedBaseMultiplier lambda (traceCutoff lambda r y)‖
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (le_max_left _ _)
  have hmr : m ≤ r := max_le (norm_trace_traceCutoff_le lambda hr x)
    (norm_trace_traceCutoff_le lambda hr y)
  have hmo : m ≤ max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ :=
    max_le_max (norm_trace_traceCutoff_le_original lambda hr x)
      (norm_trace_traceCutoff_le_original lambda hr y)
  have hm : m * |traceScale lambda r x - traceScale lambda r y| ≤
      ‖shiftedBaseMultiplier lambda (x - y)‖ :=
    (mul_le_mul_of_nonneg_right (hmr.trans (le_max_left _ _)) (abs_nonneg _)).trans
      (traceScale_difference_weighted lambda hr x y)
  change m * _ ≤ _
  calc
    _ ≤ m * (‖x - y‖ + |traceScale lambda r x - traceScale lambda r y| * ‖y‖) :=
      mul_le_mul_of_nonneg_left (norm_traceCutoff_sub_le lambda hr x y) hm0
    _ = m * ‖x - y‖ + (m * |traceScale lambda r x - traceScale lambda r y|) * ‖y‖ := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hmo (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hm (norm_nonneg _))

def LocalMixedBound (lambda : iota → NNReal) (r : ℝ) (C L : NNReal)
    (N : State iota → State iota) : Prop :=
  ∀ x y, ‖shiftedBaseMultiplier lambda x‖ ≤ r →
    ‖shiftedBaseMultiplier lambda y‖ ≤ r →
    ‖N x - N y‖ ≤ (C : ℝ) *
      (max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ * ‖x - y‖ +
        ‖shiftedBaseMultiplier lambda (x - y)‖ * ‖y‖) +
      (L : ℝ) * ‖shiftedBaseMultiplier lambda (x - y)‖

theorem LocalMixedBound.of_lipschitzOn (lambda : iota → NNReal) {r : ℝ}
    (hr : 0 ≤ r) (A : State iota → State iota →L[ℝ] State iota)
    (b : State iota → State iota) {C L : NNReal}
    (hA : LipschitzOnWith C A (Metric.closedBall 0 r))
    (hb : LipschitzOnWith L b (Metric.closedBall 0 r)) (hA0 : A 0 = 0) :
    LocalMixedBound lambda r C L (fun x =>
      A (shiftedBaseMultiplier lambda x) x + b (shiftedBaseMultiplier lambda x)) := by
  intro x y hx hy
  have hxmem : shiftedBaseMultiplier lambda x ∈ Metric.closedBall 0 r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hymem : shiftedBaseMultiplier lambda y ∈ Metric.closedBall 0 r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hzero : (0 : State iota) ∈ Metric.closedBall 0 r := by
    simpa only [Metric.mem_closedBall, dist_self] using hr
  have hcoefficient : ‖A (shiftedBaseMultiplier lambda x)‖ ≤
      (C : ℝ) * ‖shiftedBaseMultiplier lambda x‖ := by
    have h := (lipschitzOnWith_iff_dist_le_mul.mp hA)
      (shiftedBaseMultiplier lambda x) hxmem 0 hzero
    simpa only [hA0, dist_zero_right] using h
  have hcoefficientDiff :
      ‖A (shiftedBaseMultiplier lambda x) - A (shiftedBaseMultiplier lambda y)‖ ≤
        (C : ℝ) * ‖shiftedBaseMultiplier lambda (x - y)‖ := by
    simpa only [dist_eq_norm, map_sub] using
      (lipschitzOnWith_iff_dist_le_mul.mp hA)
        (shiftedBaseMultiplier lambda x) hxmem (shiftedBaseMultiplier lambda y) hymem
  have hlower :
      ‖b (shiftedBaseMultiplier lambda x) - b (shiftedBaseMultiplier lambda y)‖ ≤
        (L : ℝ) * ‖shiftedBaseMultiplier lambda (x - y)‖ := by
    simpa only [dist_eq_norm, map_sub] using
      (lipschitzOnWith_iff_dist_le_mul.mp hb)
        (shiftedBaseMultiplier lambda x) hxmem (shiftedBaseMultiplier lambda y) hymem
  have hfirst : ‖A (shiftedBaseMultiplier lambda x) (x - y)‖ ≤
      ((C : ℝ) * max ‖shiftedBaseMultiplier lambda x‖
        ‖shiftedBaseMultiplier lambda y‖) * ‖x - y‖ :=
    ((A (shiftedBaseMultiplier lambda x)).le_opNorm (x - y)).trans
      (mul_le_mul_of_nonneg_right
        (hcoefficient.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) C.coe_nonneg))
        (norm_nonneg _))
  have hsecond :
      ‖(A (shiftedBaseMultiplier lambda x) - A (shiftedBaseMultiplier lambda y)) y‖ ≤
        ((C : ℝ) * ‖shiftedBaseMultiplier lambda (x - y)‖) * ‖y‖ :=
    ((A (shiftedBaseMultiplier lambda x) -
      A (shiftedBaseMultiplier lambda y)).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hcoefficientDiff (norm_nonneg y))
  calc
    _ = ‖A (shiftedBaseMultiplier lambda x) (x - y) +
        (A (shiftedBaseMultiplier lambda x) - A (shiftedBaseMultiplier lambda y)) y +
        (b (shiftedBaseMultiplier lambda x) - b (shiftedBaseMultiplier lambda y))‖ := by
      congr 1
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      abel
    _ ≤ (‖A (shiftedBaseMultiplier lambda x) (x - y)‖ +
        ‖(A (shiftedBaseMultiplier lambda x) - A (shiftedBaseMultiplier lambda y)) y‖) +
        ‖b (shiftedBaseMultiplier lambda x) - b (shiftedBaseMultiplier lambda y)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (((C : ℝ) * max ‖shiftedBaseMultiplier lambda x‖
        ‖shiftedBaseMultiplier lambda y‖) * ‖x - y‖ +
        ((C : ℝ) * ‖shiftedBaseMultiplier lambda (x - y)‖) * ‖y‖) +
        (L : ℝ) * ‖shiftedBaseMultiplier lambda (x - y)‖ :=
      add_le_add (add_le_add hfirst hsecond) hlower
    _ = _ := by ring

theorem exists_localMixedBound_of_contDiffAt (lambda : iota → NNReal)
    (A : State iota → State iota →L[ℝ] State iota) (b : State iota → State iota)
    (hA : ContDiffAt ℝ 1 A 0) (hb : ContDiffAt ℝ 1 b 0) (hA0 : A 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C L : NNReal,
      LocalMixedBound lambda r C L (fun x =>
        A (shiftedBaseMultiplier lambda x) x + b (shiftedBaseMultiplier lambda x)) := by
  obtain ⟨C, s, hs, hAs⟩ := hA.exists_lipschitzOnWith
  obtain ⟨L, t, ht, hbt⟩ := hb.exists_lipschitzOnWith
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hs ht)
  have hsubset : Metric.closedBall (0 : State iota) (epsilon / 2) ⊆ s ∩ t := by
    intro z hz
    apply hball
    rw [Metric.mem_ball]
    exact (Metric.mem_closedBall.mp hz).trans_lt (by linarith)
  refine ⟨epsilon / 2, half_pos hepsilon, C, L, ?_⟩
  exact LocalMixedBound.of_lipschitzOn lambda (half_pos hepsilon).le A b
    (hAs.mono (fun z hz => (hsubset hz).1))
    (hbt.mono (fun z hz => (hsubset hz).2)) hA0

theorem LocalMixedBound.continuousOn {lambda : iota → NNReal} {r : ℝ}
    (hr : 0 < r) {C L : NNReal} {N : State iota → State iota}
    (hN : LocalMixedBound lambda r C L N) :
    ContinuousOn N {x | ‖shiftedBaseMultiplier lambda x‖ ≤ r} := by
  intro y hy
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  let K : ℝ := C * (r + ‖y‖) + L + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨ε / K, div_pos hε hK, ?_⟩
  intro x hx hxy
  rw [dist_eq_norm] at hxy ⊢
  have hbase := norm_shiftedBaseMultiplier_le lambda (x - y)
  have hmain : ‖N x - N y‖ ≤ K * ‖x - y‖ := by
    apply (hN x y hx hy).trans
    have hm := mul_le_mul_of_nonneg_right (max_le hx hy) (norm_nonneg (x - y))
    have hc := mul_le_mul_of_nonneg_right hbase (norm_nonneg y)
    have h := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hm hc) C.coe_nonneg)
      (mul_le_mul_of_nonneg_left hbase L.coe_nonneg)
    dsimp [K]
    nlinarith [norm_nonneg (x - y)]
  exact hmain.trans_lt ((mul_lt_mul_of_pos_left hxy hK).trans_eq (mul_div_cancel₀ ε hK.ne'))

theorem LocalMixedBound.cutoff_bound {lambda : iota → NNReal} {r : ℝ}
    (hr : 0 < r) {C L : NNReal} {N : State iota → State iota}
    (hN : LocalMixedBound lambda r C L N) (x y : State iota) :
    ‖N (traceCutoff lambda r x) - N (traceCutoff lambda r y)‖ ≤
      (3 * (C : ℝ)) *
        (max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ * ‖x - y‖ +
          ‖shiftedBaseMultiplier lambda (x - y)‖ * ‖y‖) +
        (2 * (L : ℝ)) * ‖shiftedBaseMultiplier lambda (x - y)‖ := by
  have hmain := hN (traceCutoff lambda r x) (traceCutoff lambda r y)
    (norm_trace_traceCutoff_le lambda hr x) (norm_trace_traceCutoff_le lambda hr y)
  have hhigh := weighted_norm_traceCutoff_sub_le lambda hr x y
  have htrace := norm_trace_traceCutoff_sub_le lambda hr x y
  have hcross := mul_le_mul htrace (norm_traceCutoff_le lambda hr y)
    (norm_nonneg _) (by positivity)
  have hc := mul_le_mul_of_nonneg_left (add_le_add hhigh hcross) C.coe_nonneg
  have hl := mul_le_mul_of_nonneg_left htrace L.coe_nonneg
  have hpositive : 0 ≤ (C : ℝ) *
      (max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ * ‖x - y‖) :=
    mul_nonneg C.coe_nonneg (mul_nonneg ((norm_nonneg _).trans (le_max_left _ _))
      (norm_nonneg _))
  nlinarith

def cutoffSpatialResidual (lambda : iota → NNReal) {r : ℝ} (hr : 0 < r)
    (N : State iota → State iota) (C L : NNReal)
    (hN : LocalMixedBound lambda r C L N) : SpatialResidual lambda where
  toFun x := N (traceCutoff lambda r x)
  continuous := (hN.continuousOn hr).comp_continuous (continuous_traceCutoff lambda hr)
    (fun x => norm_trace_traceCutoff_le lambda hr x)
  principalConstant := 3 * C + Real.toNNReal (1 / r)
  lowerConstant := 2 * L
  mixed x y := by
    apply (hN.cutoff_bound hr x y).trans
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat,
      Real.coe_toNNReal (1 / r) (by positivity : 0 ≤ 1 / r)]
    have hM : 0 ≤
        max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ * ‖x - y‖ +
          ‖shiftedBaseMultiplier lambda (x - y)‖ * ‖y‖ := add_nonneg
      (mul_nonneg ((norm_nonneg _).trans (le_max_left _ _)) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    nlinarith [mul_nonneg (show 0 ≤ 1 / r by positivity) hM]

theorem cutoffSpatialResidual_apply_of_small (lambda : iota → NNReal) {r : ℝ}
    (hr : 0 < r) (N : State iota → State iota) (C L : NNReal)
    (hN : LocalMixedBound lambda r C L N) {x : State iota}
    (hx : ‖shiftedBaseMultiplier lambda x‖ ≤ r) :
    (cutoffSpatialResidual lambda hr N C L hN).toFun x = N x := by
  change N (traceCutoff lambda r x) = N x
  rw [traceCutoff_eq_self lambda hr hx]

theorem cutoffSpatialResidual_forcingRadius (lambda : iota → NNReal) {r : ℝ}
    (hr : 0 < r) (N : State iota → State iota) (C L : NNReal)
    (hN : LocalMixedBound lambda r C L N) :
    2 * (cutoffSpatialResidual lambda hr N C L hN).forcingRadius < r := by
  let P : ℝ := (cutoffSpatialResidual lambda hr N C L hN).principalConstant
  have hP : 0 ≤ P := (cutoffSpatialResidual lambda hr N C L hN).principalConstant.coe_nonneg
  have hPr : 1 / r ≤ P := by
    change 1 / r ≤ ((3 * C + Real.toNNReal (1 / r) : NNReal) : ℝ)
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat,
      Real.coe_toNNReal (1 / r) (by positivity : 0 ≤ 1 / r)]
    nlinarith [C.coe_nonneg]
  have hp := (div_le_iff₀ hr).mp hPr
  change 2 * (1 / (64 * (P + 1))) < r
  rw [mul_one_div, div_lt_iff₀ (by positivity : 0 < 64 * (P + 1))]
  nlinarith

theorem cutoffSpatialResidual_response_eq {T : ℝ} (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (lambda : iota → NNReal) {r : ℝ} (hr : 0 < r)
    (N : State iota → State iota) (C L : NNReal)
    (hN : LocalMixedBound lambda r C L N) (F : ForcingSpace iota T)
    (hF : ‖F‖ ≤ (cutoffSpatialResidual lambda hr N C L hN).forcingRadius) :
    ∀ᵐ t ∂timeMeasure T,
      (cutoffSpatialResidual lambda hr N C L hN).toFun (shiftedHighOperator hT lambda F t) =
        N (shiftedHighOperator hT lambda F t) := by
  filter_upwards [intermediate_high_bound hT hT1 lambda F] with t ht
  apply cutoffSpatialResidual_apply_of_small lambda hr N C L hN
  exact ht.trans ((mul_le_mul_of_nonneg_left hF (by norm_num)).trans
    (cutoffSpatialResidual_forcingRadius lambda hr N C L hN).le)

theorem exists_spatialResidual_of_dense_core (lambda : iota → NNReal)
    (s : Set (State iota)) (hs : Dense s) (f : s → State iota) (C L : NNReal)
    (hmix : ∀ x y : s, ‖f x - f y‖ ≤ (C : ℝ) *
      (max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ *
          ‖(x : State iota) - y‖ +
        ‖shiftedBaseMultiplier lambda ((x : State iota) - y)‖ * ‖(y : State iota)‖) +
      (L : ℝ) * ‖shiftedBaseMultiplier lambda ((x : State iota) - y)‖) :
    ∃ N : SpatialResidual lambda, N.principalConstant = C ∧ N.lowerConstant = L ∧
      ∀ x : s, N.toFun x = f x := by
  let J := shiftedBaseMultiplier lambda
  let bound : State iota → State iota → ℝ := fun x y =>
    (C : ℝ) * (max ‖J x‖ ‖J y‖ * ‖x - y‖ + ‖J (x - y)‖ * ‖y‖) +
      (L : ℝ) * ‖J (x - y)‖
  have hbound_cont : Continuous (fun p : State iota × State iota => bound p.1 p.2) := by
    dsimp only [bound]
    fun_prop
  have hbounded (R : ℝ) (hR : 0 ≤ R) (x y : s)
      (hx : ‖(x : State iota)‖ ≤ R) (hy : ‖(y : State iota)‖ ≤ R) :
      ‖f x - f y‖ ≤ (2 * (C : ℝ) * R + L + 1) * ‖(x : State iota) - y‖ := by
    have htrace : ‖J ((x : State iota) - y)‖ ≤ ‖(x : State iota) - y‖ :=
      norm_shiftedBaseMultiplier_le lambda _
    have hmax : max ‖J x‖ ‖J y‖ ≤ R := max_le
      ((norm_shiftedBaseMultiplier_le lambda x).trans hx)
      ((norm_shiftedBaseMultiplier_le lambda y).trans hy)
    have htop := mul_le_mul_of_nonneg_right hmax (norm_nonneg ((x : State iota) - y))
    have hcross := mul_le_mul htrace hy (norm_nonneg (y : State iota))
      (norm_nonneg ((x : State iota) - y))
    have hC := mul_le_mul_of_nonneg_left (add_le_add htop hcross) C.coe_nonneg
    have hL := mul_le_mul_of_nonneg_left htrace L.coe_nonneg
    have h := hmix x y
    change ‖f x - f y‖ ≤ bound x y at h
    dsimp only [bound] at h
    nlinarith [norm_nonneg ((x : State iota) - y)]
  have hseq_image (x : State iota) (a : ℕ → s)
      (ha : Tendsto (fun k => (a k : State iota)) atTop (𝓝 x)) :
      ∃ z : State iota, Tendsto (fun k => f (a k)) atTop (𝓝 z) := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto _ ha).exists_norm_le
    have hRa (k : ℕ) : ‖(a k : State iota)‖ ≤ R := hR _ (mem_range_self k)
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hRa 0)
    let K : ℝ := 2 * (C : ℝ) * R + L + 1
    have hK : 0 < K := by dsimp only [K]; positivity
    apply cauchySeq_tendsto_of_complete
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.cauchySeq_iff.mp ha.cauchySeq (ε / K) (div_pos hε hK)
    refine ⟨k, ?_⟩
    intro m hm j hj
    rw [dist_eq_norm]
    apply (hbounded R hR0 (a m) (a j) (hRa m) (hRa j)).trans_lt
    have hdist := hk m hm j hj
    rw [dist_eq_norm] at hdist
    exact (mul_lt_mul_of_pos_left hdist hK).trans_eq (mul_div_cancel₀ ε hK.ne')
  have hseq (x : State iota) :
      ∃ a : ℕ → s, Tendsto (fun k => (a k : State iota)) atTop (𝓝 x) := by
    obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp (hs x)
    exact ⟨fun k => ⟨a k, ha k⟩, hlim⟩
  choose a ha using hseq
  choose N hN using fun x => hseq_image x (a x) (ha x)
  have hlimit {x y u v : State iota} (p q : ℕ → s)
      (hp : Tendsto (fun k => (p k : State iota)) atTop (𝓝 x))
      (hq : Tendsto (fun k => (q k : State iota)) atTop (𝓝 y))
      (hfp : Tendsto (fun k => f (p k)) atTop (𝓝 u))
      (hfq : Tendsto (fun k => f (q k)) atTop (𝓝 v)) : ‖u - v‖ ≤ bound x y := by
    apply le_of_tendsto_of_tendsto (hfp.sub hfq).norm
      ((hbound_cont.tendsto (x, y)).comp (hp.prodMk_nhds hq))
    exact Eventually.of_forall (fun k => hmix (p k) (q k))
  have hNmix (x y : State iota) : ‖N x - N y‖ ≤ bound x y :=
    hlimit (a x) (a y) (ha x) (ha y) (hN x) (hN y)
  have hNcont : Continuous N := by
    apply continuous_iff_continuousAt.mpr
    intro x
    let r : ℝ := ‖J x‖ + 1
    have hr : 0 < r := by dsimp only [r]; positivity
    have hlocal : LocalMixedBound lambda r C L N := fun y z _ _ => hNmix y z
    apply (hlocal.continuousOn hr).continuousAt
    exact (J.continuous.norm.continuousAt).preimage_mem_nhds
      (Iic_mem_nhds (by dsimp only [r]; linarith : ‖J x‖ < r))
  refine ⟨{
    toFun := N
    continuous := hNcont
    principalConstant := C
    lowerConstant := L
    mixed := hNmix }, rfl, rfl, ?_⟩
  intro x
  have h := hlimit (a x) (fun _ => x) (ha x) tendsto_const_nhds
    (hN x) tendsto_const_nhds
  have hz : ‖N x - f x‖ ≤ 0 := by simpa only [bound, sub_self, map_zero,
    norm_zero, mul_zero, zero_mul, add_zero] using h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

theorem exists_spatialResidual_of_dense_local_core (lambda : iota → NNReal)
    (S : Submodule ℝ (State iota)) (hS : Dense (S : Set (State iota)))
    {r : ℝ} (hr : 0 < r) (C L : NNReal)
    (f : {x : S // ‖shiftedBaseMultiplier lambda (x : State iota)‖ ≤ r} → State iota)
    (hmix : ∀ x y, ‖f x - f y‖ ≤ (C : ℝ) *
      (max ‖shiftedBaseMultiplier lambda (x.val : State iota)‖
          ‖shiftedBaseMultiplier lambda (y.val : State iota)‖ *
          ‖(x.val : State iota) - y.val‖ +
        ‖shiftedBaseMultiplier lambda ((x.val : State iota) - y.val)‖ *
          ‖(y.val : State iota)‖) +
      (L : ℝ) * ‖shiftedBaseMultiplier lambda ((x.val : State iota) - y.val)‖) :
    ∃ N : SpatialResidual lambda,
      N.principalConstant = 3 * C + Real.toNNReal (1 / r) ∧
      N.lowerConstant = 2 * L ∧
      (∀ (x : S) (hx : ‖shiftedBaseMultiplier lambda (x : State iota)‖ ≤ r),
        N.toFun x = f ⟨x, hx⟩) ∧
      2 * N.forcingRadius < r := by
  let cut (x : S) : {y : S // ‖shiftedBaseMultiplier lambda (y : State iota)‖ ≤ r} :=
    ⟨⟨traceCutoff lambda r x, S.smul_mem (traceScale lambda r x) x.property⟩,
      norm_trace_traceCutoff_le lambda hr x⟩
  have hglobal (x y : S) : ‖f (cut x) - f (cut y)‖ ≤
      ((3 * C + Real.toNNReal (1 / r) : NNReal) : ℝ) *
        (max ‖shiftedBaseMultiplier lambda (x : State iota)‖
            ‖shiftedBaseMultiplier lambda (y : State iota)‖ *
            ‖(x : State iota) - y‖ +
          ‖shiftedBaseMultiplier lambda ((x : State iota) - y)‖ * ‖(y : State iota)‖) +
        ((2 * L : NNReal) : ℝ) *
          ‖shiftedBaseMultiplier lambda ((x : State iota) - y)‖ := by
    have hmain := hmix (cut x) (cut y)
    change ‖f (cut x) - f (cut y)‖ ≤ (C : ℝ) *
      (max ‖shiftedBaseMultiplier lambda (traceCutoff lambda r x)‖
          ‖shiftedBaseMultiplier lambda (traceCutoff lambda r y)‖ *
          ‖traceCutoff lambda r x - traceCutoff lambda r y‖ +
        ‖shiftedBaseMultiplier lambda (traceCutoff lambda r x - traceCutoff lambda r y)‖ *
          ‖traceCutoff lambda r y‖) +
      (L : ℝ) *
        ‖shiftedBaseMultiplier lambda (traceCutoff lambda r x - traceCutoff lambda r y)‖
      at hmain
    have hhigh := weighted_norm_traceCutoff_sub_le lambda hr x y
    have htrace := norm_trace_traceCutoff_sub_le lambda hr x y
    have hcross := mul_le_mul htrace (norm_traceCutoff_le lambda hr y)
      (norm_nonneg _) (by positivity)
    have hc := mul_le_mul_of_nonneg_left (add_le_add hhigh hcross) C.coe_nonneg
    have hl := mul_le_mul_of_nonneg_left htrace L.coe_nonneg
    have hpositive : 0 ≤ (C : ℝ) *
        (max ‖shiftedBaseMultiplier lambda (x : State iota)‖
          ‖shiftedBaseMultiplier lambda (y : State iota)‖ * ‖(x : State iota) - y‖) :=
      mul_nonneg C.coe_nonneg
        (mul_nonneg ((norm_nonneg _).trans (le_max_left _ _)) (norm_nonneg _))
    have hM : 0 ≤
        max ‖shiftedBaseMultiplier lambda (x : State iota)‖
          ‖shiftedBaseMultiplier lambda (y : State iota)‖ * ‖(x : State iota) - y‖ +
        ‖shiftedBaseMultiplier lambda ((x : State iota) - y)‖ * ‖(y : State iota)‖ :=
      add_nonneg
        (mul_nonneg ((norm_nonneg _).trans (le_max_left _ _)) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat,
      Real.coe_toNNReal (1 / r) (by positivity : 0 ≤ 1 / r)]
    nlinarith [mul_nonneg (show 0 ≤ 1 / r by positivity) hM]
  obtain ⟨N, hC, hL, hN⟩ := exists_spatialResidual_of_dense_core lambda S hS
    (fun x => f (cut x)) (3 * C + Real.toNNReal (1 / r)) (2 * L) hglobal
  refine ⟨N, hC, hL, ?_, ?_⟩
  · intro x hx
    rw [hN x]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact traceCutoff_eq_self lambda hr hx
  · have hP : 0 ≤ (N.principalConstant : ℝ) := N.principalConstant.coe_nonneg
    have hPr : 1 / r ≤ (N.principalConstant : ℝ) := by
      rw [hC]
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat,
        Real.coe_toNNReal (1 / r) (by positivity : 0 ≤ 1 / r)]
      nlinarith [C.coe_nonneg]
    have hp := (div_le_iff₀ hr).mp hPr
    change 2 * (1 / (64 * ((N.principalConstant : ℝ) + 1))) < r
    rw [mul_one_div, div_lt_iff₀ (by positivity : 0 < 64 * ((N.principalConstant : ℝ) + 1))]
    nlinarith

end PoincareConjecture.QuasilinearDeTurckNative
