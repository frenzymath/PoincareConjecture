import PoincareConjecture.Proofs.M47.NoncollapseHorizonTested
import Mathlib.Analysis.Complex.ExponentialBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem seed_volume_of_near_nonpositive_ancestor
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    {J : Set ℝ} {T kappa r : ℝ}
    (hnoncollapse : SurgeryNoncollapsedOn F J kappa)
    (x : (F.slice T).carrier) (hr : 0 < r) (hrepsilon : r ≤ F.parameters.epsilon)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
      ((F.metric T).ball x r))
    (hbased : ∀ hs y, y ∈ (F.metric T).ball x r → HEq (e.forward 0 hs y) y)
    (hcurv : ∀ s hs y, y ∈ (F.metric T).ball x r →
      (F.connection (T + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤ r⁻¹ ^ 2)
    {s : ℝ} (hs : s ∈ Icc (-r ^ 2) 0) (hnear : -r ^ 2 / 8 ≤ s)
    (hJ : T + s / 1 ∈ J)
    (hnonpositive : ¬ SurgeryPositiveComponentAt F (T + s / 1) (e.forward s hs x)) :
    ENNReal.ofReal ((kappa / 512) * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  let q := r / 4
  let R := r / 2
  have hq : 0 < q := by dsimp only [q]; positivity
  have hR : 0 < R := half_pos hr
  have hqr : q < r := by dsimp only [q]; linarith only [hr]
  have hRr : R < r := half_lt_self hr
  have hquot : R / 2 = q := by dsimp only [R, q]; ring
  have hfactor : Real.exp (6 * r⁻¹ ^ 2 * (-s)) ≤ (2 : ℝ) ^ 2 := by
    have hcancel : r⁻¹ ^ 2 * r ^ 2 = 1 := by field_simp
    have hbound := mul_le_mul_of_nonneg_left
      (show -s ≤ r ^ 2 / 8 by linarith only [hnear])
      (show 0 ≤ 6 * r⁻¹ ^ 2 by positivity)
    have hexponent : 6 * r⁻¹ ^ 2 * (-s) ≤ 1 := by nlinarith only [hbound, hcancel]
    exact (Real.exp_le_exp.mpr hexponent).trans
      (Real.exp_one_lt_three.le.trans (by norm_num))
  let U : TopologicalSpace.Opens (F.slice T).carrier :=
    ⟨(F.metric T).ball x r, isOpen_Iio.preimage
      ((M36.metric_edist_continuous (F.metric T)).comp
        (continuous_const.prodMk continuous_id))⟩
  have hxU : x ∈ U := by
    change (F.metric T).edist x x < ENNReal.ofReal r
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hmetric := horizon_cylinder_metric_comparison P (neg_neg_of_pos (sq_pos_of_pos hr))
    (sq_nonneg r⁻¹) U ⟨x, hxU⟩ e hbased hcurv hs hfactor
  let D := M44.cylinderSliceChart e U.isOpen s hs
  have hlower (y : (F.slice T).carrier) (hy : y ∈ D.source)
      (v : TangentSpace (𝓡 3) y) :
      (F.metric T).inner y v v ≤ (2 : ℝ) ^ 2 * (F.metric (T + s / 1)).inner (D y)
        (mfderiv (𝓡 3) (𝓡 3) D y v) (mfderiv (𝓡 3) (𝓡 3) D y v) := by
    simpa only [D, M44.cylinderSliceChart, SurgeryFlowCylinder.pullbackInner, one_mul]
      using (hmetric y hy v).1
  have hupper (y : (F.slice T).carrier) (hy : y ∈ D.source)
      (v : TangentSpace (𝓡 3) y) :
      (F.metric (T + s / 1)).inner (D y)
        (mfderiv (𝓡 3) (𝓡 3) D y v) (mfderiv (𝓡 3) (𝓡 3) D y v) ≤
          (2 : ℝ) ^ 2 * (F.metric T).inner y v v := by
    simpa only [D, M44.cylinderSliceChart, SurgeryFlowCylinder.pullbackInner, one_mul]
      using (hmetric y hy v).2
  have hT : T ∈ F.time_domain := by
    simpa only [zero_div, add_zero] using
      e.time_subset (mem_image_of_mem _ (show (0 : ℝ) ∈ Icc (-r ^ 2) 0 from
        ⟨neg_nonpos.mpr (sq_nonneg r), le_rfl⟩))
  have hcompact : IsCompact (closure ((F.metric T).ball x R)) :=
    (F.slices_compact T hT).of_isClosed_subset isClosed_closure (subset_univ _)
  have hsource : closure ((F.metric T).ball x R) ⊆ D.source :=
    (F.metric T).closure_ball_subset_ball_of_lt x hr hRr
  have hcover := horizon_ball_subset_image (F.metric T) (F.metric (T + s / 1))
    D (by norm_num : (0 : ℝ) < 2) hlower x hR hcompact hsource
  rw [hquot] at hcover
  let V := (F.metric (T + s / 1)).ball (e.forward s hs x) q
  have hV : V ⊆ e.forward s hs '' (U : Set (F.slice T).carrier) :=
    hcover.trans (image_mono (subset_closure.trans hsource))
  have hrange : ∀ u ∈ Icc (-q ^ 2) 0, s + 1 * u ∈ Icc (-r ^ 2) 0 := by
    intro u hu
    dsimp only [q] at hu
    constructor <;> nlinarith only [hu.1, hu.2, hnear, hs.2, sq_nonneg r]
  obtain ⟨d, hdbased, hdcurv⟩ := exists_seedCylinder_recenter e U.isOpen s hs hrange V hV hcurv
  have htest : r⁻¹ ^ 2 ≤ q⁻¹ ^ 2 := pow_le_pow_left₀ (inv_pos.mpr hr).le
    ((inv_le_inv₀ hr hq).mpr hqr.le) 2
  have hvolume := hnoncollapse (T + s / 1) hJ (e.time_subset (mem_image_of_mem _ hs))
    (e.forward s hs x) hnonpositive q hq (hqr.le.trans hrepsilon) d hdbased
      (fun u hu y hy => (hdcurv u hu y hy).trans htest)
  have hcompare := horizon_target_ball_volume_le_source (F.metric T) (F.metric (T + s / 1))
    D (by norm_num : (0 : ℝ) < 2) hlower hupper x hR hcompact hsource
  rw [hquot] at hcompare
  have hball : (F.metric T).ball x R ⊆ (F.metric T).ball x r :=
    subset_closure.trans hsource
  have hbound := hvolume.trans (hcompare.trans (mul_le_mul' le_rfl (measure_mono hball)))
  have hcancel : ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (2 : ℝ) ^ 3 = 1 := by
    rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
    norm_num
  calc
    ENNReal.ofReal ((kappa / 512) * r ^ 3) =
        ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (kappa * q ^ 3) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      congr 1
      dsimp only [q]
      ring
    _ ≤ ENNReal.ofReal (1 / 8 : ℝ) * (ENNReal.ofReal (2 : ℝ) ^ 3 *
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r)) :=
      mul_le_mul_right hbound _
    _ = _ := by rw [← mul_assoc, hcancel, one_mul]

end PoincareConjecture.Proofs.M47
