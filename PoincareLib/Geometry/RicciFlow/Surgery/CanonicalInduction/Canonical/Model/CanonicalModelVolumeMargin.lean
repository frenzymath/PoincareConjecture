import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Volume.VolumeBoundary
import Mathlib.Topology.Order.Compact

/-!
# A uniform model-volume ratio arbitrarily close to one

Morgan--Tian Theorem 1.34, p. 19, and Proposition 9.79, pp. 232-234.
The exact comparison model varies continuously on a compact positive
radius interval. Its ratio absorbs both nearby metric and radius losses
while preserving a prescribed strict cap-density margin.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareMT.Proofs.M47

/-- One radius factor greater than one works throughout the compact old
radius interval, using the exact Bishop--Gromov model, Proposition 9.79. -/
theorem exists_model_volume_ratio_margin {kappa a b q : ℝ}
    (hkappa : 0 ≤ kappa) (ha : 0 < a) (_hq : 0 < q) (hq1 : q < 1) :
    ∃ Lambda : ℝ, 1 < Lambda ∧ ∀ R ∈ Icc a b,
      q * Lambda ^ 6 < RiemannianMetric.modelVolume 3 kappa (R / Lambda ^ 2) /
        RiemannianMetric.modelVolume 3 kappa R := by
  let V := RiemannianMetric.modelVolume 3 kappa
  have hV : Continuous V := RiemannianMetric.continuous_modelVolume 3 kappa
  have hnear : ∀ᶠ Lambda : ℝ in 𝓝 1, ∀ R ∈ Icc a b,
      q * Lambda ^ 6 < V (R / Lambda ^ 2) / V R := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro R hR
    have hVpos : 0 < V R :=
      RiemannianMetric.modelVolume_pos (by norm_num : 1 ≤ 3) hkappa (ha.trans_le hR.1)
    have hdivide : ContinuousAt (fun p : ℝ × ℝ => p.2 / p.1 ^ 2) (1, R) :=
      continuousAt_snd.div (continuousAt_fst.pow 2) (by norm_num)
    have hratio : ContinuousAt (fun p : ℝ × ℝ => V (p.2 / p.1 ^ 2) / V p.2) (1, R) :=
      (hV.continuousAt.comp hdivide).div
        (hV.continuousAt.comp continuousAt_snd) hVpos.ne'
    have hleft : ContinuousAt (fun p : ℝ × ℝ => q * p.1 ^ 6) (1, R) :=
      continuousAt_const.mul (continuousAt_fst.pow 6)
    exact hleft.eventually_lt hratio (by
      change q * (1 : ℝ) ^ 6 < V (R / (1 : ℝ) ^ 2) / V R
      simpa only [one_pow, mul_one, div_one, div_self hVpos.ne'] using hq1)
  have hright : ∀ᶠ Lambda : ℝ in 𝓝[>] 1,
      1 < Lambda ∧ ∀ R ∈ Icc a b, q * Lambda ^ 6 < V (R / Lambda ^ 2) / V R :=
    Filter.Eventually.and
      (self_mem_nhdsWithin : ∀ᶠ Lambda : ℝ in 𝓝[>] 1, Lambda ∈ Ioi 1)
      (hnear.filter_mono nhdsWithin_le_nhds)
  exact hright.exists

end PoincareMT.Proofs.M47
