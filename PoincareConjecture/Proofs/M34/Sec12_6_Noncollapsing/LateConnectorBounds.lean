import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.EarlyCoordinatePacket
import PoincareConjecture.Proofs.M34.Standard.ReducedLengthConnector
import PoincareConjecture.Proofs.M10.ScalarBound

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

namespace PoincareConjecture.M34

open Proofs.M09

theorem late_square_time_gap {L t : ℝ} (hL : 0 < L) (ht : t ∈ Ico (L / 2) L) :
    (L / 8) / (2 * Real.sqrt L) ≤ Real.sqrt (t - L / 8) - Real.sqrt (t - L / 4) := by
  have h1 : 0 < t - L / 4 := by linarith [ht.1]
  have h0 : 0 < t - L / 8 := by linarith [ht.1]
  have hgap : 0 ≤ Real.sqrt (t - L / 8) - Real.sqrt (t - L / 4) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hsum : Real.sqrt (t - L / 8) + Real.sqrt (t - L / 4) ≤ 2 * Real.sqrt L := by
    have ha := Real.sqrt_le_sqrt (show t - L / 8 ≤ L by linarith [ht.2])
    have hb := Real.sqrt_le_sqrt (show t - L / 4 ≤ L by linarith [ht.2])
    linarith
  apply (div_le_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr hL))).mpr
  have hprod := mul_le_mul_of_nonneg_left hsum hgap
  nlinarith [Real.sq_sqrt h0.le, Real.sq_sqrt h1.le]

theorem late_connector_time_mem {L t s : ℝ} (hL : 0 < L) (ht : t ∈ Ico (L / 2) L)
    (hs : s ∈ Icc (Real.sqrt (t - L / 4)) (Real.sqrt (t - L / 8))) :
    t - s ^ 2 ∈ Icc (L / 8) (L / 4) ∧ s ^ 2 ≤ L := by
  have h1 : 0 ≤ t - L / 4 := by linarith [ht.1]
  have h0 : 0 ≤ t - L / 8 := by linarith [ht.1]
  have hs0 : 0 ≤ s := (Real.sqrt_nonneg _).trans hs.1
  have hlow := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs.1 2
  have hupp := pow_le_pow_left₀ hs0 hs.2 2
  rw [Real.sq_sqrt h1] at hlow
  rw [Real.sq_sqrt h0] at hupp
  constructor
  · constructor <;> linarith
  · linarith [ht.2]

theorem late_coordinate_connector_action_le {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : RicciFlowCurvatureTheory.{0})
    {delta d C K : ℝ} (hdelta : 0 < delta) (hd : 0 < d) (hC : 1 ≤ C) (hK : 0 ≤ K)
    (htransition : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C)
    (hcurv : ∀ u ∈ Icc 0 (F.lifetime / 2), ∀ x : StandardCapSpace,
      |(F.flow.connection u).curvatureTensorNorm x| ≤ K)
    (f : StandardCapSpace → StandardCapSpace)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 delta))
    (hdiff : ∀ u ∈ Icc 0 (F.lifetime / 2), ∀ x ∈ Metric.ball 0 delta,
      ∀ v : StandardCapSpace,
        (F.flow.metric u).tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ d * ‖v‖)
    {t : ℝ} (ht : t ∈ Ico (F.lifetime / 2) F.lifetime) {z : StandardCapSpace}
    (hz : z ∈ Metric.ball 0 delta) :
    let speed := d * (C / ((F.lifetime / 8) / (2 * Real.sqrt F.lifetime))) * delta
    let A := 2 * F.lifetime * (9 * K) + speed ^ 2 / 2
    (∫ s in Real.sqrt (t - F.lifetime / 4)..Real.sqrt (t - F.lifetime / 8),
      squareCurveActionDensity F.flow t
        (coordinateConnector f (Real.sqrt (t - F.lifetime / 4))
          (Real.sqrt (t - F.lifetime / 8)) z) s) ≤ A * Real.sqrt F.lifetime := by
  dsimp only
  have hL := F.lifetime_pos
  let speed := d * (C / ((F.lifetime / 8) / (2 * Real.sqrt F.lifetime))) * delta
  let A := 2 * F.lifetime * (9 * K) + speed ^ 2 / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h1 : 0 < t - F.lifetime / 4 := by linarith [ht.1, F.lifetime_pos]
  have h0 : 0 < t - F.lifetime / 8 := by linarith [ht.1, F.lifetime_pos]
  have h10 : t - F.lifetime / 4 < t - F.lifetime / 8 := by linarith [F.lifetime_pos]
  have hab := Real.sqrt_lt_sqrt h1.le h10
  have hmin : 0 < (F.lifetime / 8) / (2 * Real.sqrt F.lifetime) := by
    exact div_pos (by linarith [F.lifetime_pos])
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr F.lifetime_pos))
  let beta := coordinateConnector f (Real.sqrt (t - F.lifetime / 4))
    (Real.sqrt (t - F.lifetime / 8)) z
  have hbound : ∀ s ∈ Icc (Real.sqrt (t - F.lifetime / 4))
      (Real.sqrt (t - F.lifetime / 8)), squareCurveActionDensity F.flow t beta s ≤ A := by
    intro s hs
    obtain ⟨hphys, hsL⟩ := late_connector_time_mem F.lifetime_pos ht hs
    have htime : t - s ^ 2 ∈ Icc 0 (F.lifetime / 2) := by
      constructor <;> linarith [hphys.1, hphys.2, F.lifetime_pos]
    have hscalar : (F.flow.connection (t - s ^ 2)).scalarCurvature (beta s) ≤ 9 * K := by
      have h := M10.abs_scalarCurvature_le (F.flow.metric (t - s ^ 2))
        (F.flow.connection (t - s ^ 2)) (beta s)
      norm_num at h
      exact (le_abs_self _).trans (h.trans (mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hcurv _ htime _)) (by norm_num)))
    have hspeed := coordinateConnector_tangentNorm_le (F.flow.metric (t - s ^ 2)) f
      hab hd.le (zero_le_one.trans hC) htransition hz hf (hdiff _ htime) s
    have hspeed' : (F.flow.metric (t - s ^ 2)).tangentNorm (beta s)
        (curveVelocity beta s) ≤ speed := hspeed.trans (by
      dsimp [speed]
      gcongr
      exact late_square_time_gap F.lifetime_pos ht)
    exact squareCurveActionDensity_le_of_tangentNorm_le F.flow t beta s
      (mul_nonneg (by norm_num) hK) hsL hscalar hspeed'
  have hwindow : Icc (t - t) t ⊆ Ico 0 F.lifetime := by
    intro u hu
    exact ⟨by linarith [hu.1], hu.2.trans_lt ht.2⟩
  have hi := squareCurveActionIntegral_le F.flow P t t
    (by linarith [ht.1, F.lifetime_pos]) hwindow h0
    (by linarith [F.lifetime_pos]) (Real.sqrt_nonneg _) hab.le beta
    (coordinateConnector_contMDiff f _ _ hz hf) hbound
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ hA
  have hroot := Real.sqrt_le_sqrt (show t - F.lifetime / 8 ≤ F.lifetime by
    linarith [ht.2, F.lifetime_pos])
  linarith [Real.sqrt_nonneg (t - F.lifetime / 4)]

end PoincareConjecture.M34
