import PoincareConjecture.Proofs.M34.Standard.GeneralizedVolumeRatio
import PoincareConjecture.Proofs.M34.Standard.CalibratedBishopGromov










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.GeneralizedBlowupConvergence

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

local instance : TopologicalSpace C.limit.carrier.carrier := C.limit.carrier.topologicalSpace
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold
local instance : MeasurableSpace C.limit.carrier.carrier := C.limit.carrier.measurableSpace
local instance : BorelSpace C.limit.carrier.carrier := C.limit.carrier.borelSpace
local instance : T3Space C.limit.carrier.carrier := C.limit.carrier.t3Space




theorem eventually_fixed_ball_volume_lt_of_zero_avr
    (hzero : asymptoticVolumeRatio (C.limit.flow.metric 0) C.limit.base = 0)
    (hBG : ∀ᶠ k : ℕ in atTop, AntitoneMetricBallVolumeRatio
      ((S.flow (C.subsequence k)).metric (S.base (C.subsequence k)).1)
        (S.base (C.subsequence k)).2)
    {D v : ℝ} (hD : 0 < D) (hv : 0 < v) :
    ∀ᶠ k : ℕ in atTop,
      calibratedMetricVolume ((S.flow (C.subsequence k)).metric (S.base (C.subsequence k)).1)
        (((S.flow (C.subsequence k)).metric (S.base (C.subsequence k)).1).ball
          (S.base (C.subsequence k)).2 D) < ENNReal.ofReal v := by
  have heta : 0 < v / (64 * D ^ 3) := div_pos hv (mul_pos (by norm_num) (pow_pos hD 3))
  have hinf : sInf (range (metricBallVolumeRatio (C.limit.flow.metric 0) C.limit.base)) <
      ENNReal.ofReal (v / (64 * D ^ 3)) := by
    change asymptoticVolumeRatio (C.limit.flow.metric 0) C.limit.base < _
    rw [hzero]
    exact ENNReal.ofReal_pos.mpr heta
  obtain ⟨w, ⟨rho, rfl⟩, hrho⟩ := sInf_lt_iff.mp hinf
  let a : ℝ := rho / 2
  have ha : 0 < a := div_pos rho.2 two_pos
  have hdouble : (⟨2 * a, mul_pos two_pos ha⟩ : PositiveRadius) = rho := by
    apply Subtype.ext
    dsimp [a]
    ring
  have hdiv : Tendsto (fun k => S.scale (C.subsequence k)) atTop atTop :=
    S.scalar_diverges.comp C.subsequence_strictMono.tendsto_atTop
  filter_upwards [hBG, C.eventually_source_ball_volume_ratio_le_zero a ha,
    hdiv.eventually_gt_atTop ((a / D) ^ 2)] with k hbg hratio hscale
  rw [hdouble] at hratio
  have hq : 0 < Real.sqrt (S.scale (C.subsequence k)) :=
    Real.sqrt_pos.mpr (S.base_scalar_pos (C.subsequence k))
  have hr : 0 < a / Real.sqrt (S.scale (C.subsequence k)) := div_pos ha hq
  have hrD : a / Real.sqrt (S.scale (C.subsequence k)) < D := by
    apply (div_lt_iff₀ hq).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hD).mp
      ((Real.lt_sqrt (div_nonneg ha.le hD.le)).mpr hscale)
  have h64 : 64 * metricBallVolumeRatio (C.limit.flow.metric 0) C.limit.base rho <
      ENNReal.ofReal (v / D ^ 3) := by
    have hmul := ENNReal.mul_lt_mul_left (a := 64) (by norm_num) (by norm_num) hrho
    have heq : ENNReal.ofReal (v / (64 * D ^ 3)) * 64 =
        ENNReal.ofReal (v / D ^ 3) := by
      rw [← ENNReal.ofReal_ofNat (n := 64), ← ENNReal.ofReal_mul heta.le]
      congr 1
      field_simp
    calc
      _ = metricBallVolumeRatio (C.limit.flow.metric 0) C.limit.base rho * 64 := mul_comm _ _
      _ < ENNReal.ofReal (v / (64 * D ^ 3)) * 64 := hmul
      _ = _ := heq
  have hnorm : metricBallVolumeRatio
      ((S.flow (C.subsequence k)).metric (S.base (C.subsequence k)).1)
      (S.base (C.subsequence k)).2 ⟨D, hD⟩ < ENNReal.ofReal (v / D ^ 3) :=
    (hbg (show (⟨a / Real.sqrt (S.scale (C.subsequence k)), hr⟩ : PositiveRadius) ≤
      ⟨D, hD⟩ from hrD.le)).trans_lt (hratio.trans_lt h64)
  have hd0 : ENNReal.ofReal D ^ 3 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hD).ne'
  have hdtop : ENNReal.ofReal D ^ 3 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hvolume := (ENNReal.div_lt_iff (Or.inl hd0) (Or.inl hdtop)).mp hnorm
  have hcancel : ENNReal.ofReal (v / D ^ 3) * ENNReal.ofReal D ^ 3 =
      ENNReal.ofReal v := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hD 3), ENNReal.ofReal_pow hD.le,
      ENNReal.div_mul_cancel hd0 hdtop]
  exact hvolume.trans_eq hcancel

end PoincareConjecture.GeneralizedBlowupConvergence
