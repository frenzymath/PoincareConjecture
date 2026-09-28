import PoincareConjecture.Proofs.M47.NoncollapseHorizonMetric
import PoincareConjecture.Proofs.M47.NoncollapseHorizonScales
import PoincareConjecture.Proofs.M47.SeedCylinderRecenter
import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlBalls










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem horizon_tested_volume_of_interior
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {a T kappa r : ℝ}
    (haT : a < T) (x : (F.slice T).carrier) (hr : 0 < r)
    (hrepsilon : r ≤ F.parameters.epsilon)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
      ((F.metric T).ball x r))
    (hbased : ∀ hs y, y ∈ (F.metric T).ball x r → HEq (e.forward 0 hs y) y)
    (hcurv : ∀ s hs y, y ∈ (F.metric T).ball x r →
      (F.connection (T + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤ r⁻¹ ^ 2)
    (hinterior : ∀ (s : ℝ) (hs : s ∈ Icc (-r ^ 2) 0), s < 0 → a ≤ T + s / 1 →
      ∀ q : ℝ, 0 < q → q ≤ F.parameters.epsilon →
      ∀ d : SurgeryFlowCylinder F (F.slice (T + s / 1)) (T + s / 1) 1
        (Icc (-q ^ 2) 0) ((F.metric (T + s / 1)).ball (e.forward s hs x) q),
        (∀ h y, y ∈ (F.metric (T + s / 1)).ball (e.forward s hs x) q →
          HEq (d.forward 0 h y) y) →
        (∀ u hu y, y ∈ (F.metric (T + s / 1)).ball (e.forward s hs x) q →
          (F.connection ((T + s / 1) + u / 1)).curvatureTensorNorm
            (d.forward u hu y) ≤ q⁻¹ ^ 2) →
        ENNReal.ofReal (kappa * q ^ 3) ≤ calibratedMetricVolume (F.metric (T + s / 1))
          ((F.metric (T + s / 1)).ball (e.forward s hs x) q)) :
    ENNReal.ofReal (kappa * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  apply horizon_volume_of_contracted_densities
  intro theta htheta
  let q := theta ^ 2 * r
  let R := theta * r
  let C := theta⁻¹
  have hq : 0 < q := mul_pos (sq_pos_of_pos htheta.1) hr
  have hR : 0 < R := mul_pos htheta.1 hr
  have hthetaSq : theta ^ 2 < 1 := by nlinarith only [htheta.1, htheta.2]
  have hqr : q < r := by
    simpa only [q, one_mul] using mul_lt_mul_of_pos_right hthetaSq hr
  have hRr : R < r := by
    simpa only [R, one_mul] using mul_lt_mul_of_pos_right htheta.2 hr
  have hC : 1 < C := by
    change 1 < theta⁻¹
    rw [← one_div]
    exact (lt_div_iff₀ htheta.1).mpr (by simpa only [one_mul] using htheta.2)
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hquot : R / C = q := by
    dsimp only [R, C, q]
    rw [div_inv_eq_mul]
    ring
  obtain ⟨s, hs, haS, hbackward, hfactor⟩ :=
    exists_horizon_earlier_parameter haT hr hq hqr hC
  have hsI : s ∈ Icc (-r ^ 2) 0 := Ioo_subset_Icc_self hs
  let U : TopologicalSpace.Opens (F.slice T).carrier :=
    ⟨(F.metric T).ball x r, isOpen_Iio.preimage
      ((M36.metric_edist_continuous (F.metric T)).comp
        (continuous_const.prodMk continuous_id))⟩
  have hxU : x ∈ U := by
    change (F.metric T).edist x x < ENNReal.ofReal r
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hmetric := horizon_cylinder_metric_comparison P (neg_neg_of_pos (sq_pos_of_pos hr))
    (sq_nonneg r⁻¹) U ⟨x, hxU⟩ e hbased hcurv hsI hfactor
  let D := M44.cylinderSliceChart e U.isOpen s hsI
  have hlower (y : (F.slice T).carrier) (hy : y ∈ D.source)
      (v : TangentSpace (𝓡 3) y) :
      (F.metric T).inner y v v ≤ C ^ 2 * (F.metric (T + s / 1)).inner (D y)
        (mfderiv (𝓡 3) (𝓡 3) D y v) (mfderiv (𝓡 3) (𝓡 3) D y v) := by
    simpa only [D, M44.cylinderSliceChart, SurgeryFlowCylinder.pullbackInner, one_mul]
      using (hmetric y hy v).1
  have hupper (y : (F.slice T).carrier) (hy : y ∈ D.source)
      (v : TangentSpace (𝓡 3) y) :
      (F.metric (T + s / 1)).inner (D y)
        (mfderiv (𝓡 3) (𝓡 3) D y v) (mfderiv (𝓡 3) (𝓡 3) D y v) ≤
          C ^ 2 * (F.metric T).inner y v v := by
    simpa only [D, M44.cylinderSliceChart, SurgeryFlowCylinder.pullbackInner, one_mul]
      using (hmetric y hy v).2
  have hT : T ∈ F.time_domain := by
    simpa only [zero_div, add_zero] using
      e.time_subset (mem_image_of_mem _ (show (0 : ℝ) ∈ Icc (-r ^ 2) 0 from
        ⟨by nlinarith only [sq_nonneg r], le_rfl⟩))
  have hcompact : IsCompact (closure ((F.metric T).ball x R)) :=
    (F.slices_compact T hT).of_isClosed_subset isClosed_closure (subset_univ _)
  have hsource : closure ((F.metric T).ball x R) ⊆ D.source :=
    (F.metric T).closure_ball_subset_ball_of_lt x hr hRr
  have hcover := horizon_ball_subset_image (F.metric T) (F.metric (T + s / 1))
    D hCpos hlower x hR hcompact hsource
  rw [hquot] at hcover
  let V := (F.metric (T + s / 1)).ball (e.forward s hsI x) q
  have hV : V ⊆ e.forward s hsI '' (U : Set (F.slice T).carrier) :=
    hcover.trans (image_mono (subset_closure.trans hsource))
  have hrange : ∀ u ∈ Icc (-q ^ 2) 0, s + 1 * u ∈ Icc (-r ^ 2) 0 := by
    intro u hu
    constructor <;> linarith only [hu.1, hu.2, hbackward, hs.2]
  obtain ⟨d, hdbased, hdcurv⟩ := exists_seedCylinder_recenter e U.isOpen s hsI hrange V hV hcurv
  have htest : r⁻¹ ^ 2 ≤ q⁻¹ ^ 2 := pow_le_pow_left₀ (inv_pos.mpr hr).le
    ((inv_le_inv₀ hr hq).mpr hqr.le) 2
  have hvolume := hinterior s hsI hs.2 (by simpa only [div_one] using haS)
    q hq (hqr.le.trans hrepsilon) d hdbased
      (fun u hu y hy => (hdcurv u hu y hy).trans htest)
  have hcompare := horizon_target_ball_volume_le_source (F.metric T) (F.metric (T + s / 1))
    D hCpos hlower hupper x hR hcompact hsource
  rw [hquot] at hcompare
  have hball : (F.metric T).ball x R ⊆ (F.metric T).ball x r :=
    subset_closure.trans hsource
  have hbound := hvolume.trans (hcompare.trans (mul_le_mul' le_rfl (measure_mono hball)))
  have hcancel : ENNReal.ofReal (theta ^ 3) * ENNReal.ofReal C ^ 3 = 1 := by
    rw [← ENNReal.ofReal_pow hCpos.le,
      ← ENNReal.ofReal_mul (pow_nonneg htheta.1.le 3)]
    have heq : theta ^ 3 * C ^ 3 = 1 := by
      dsimp only [C]
      field_simp [htheta.1.ne']
    rw [heq, ENNReal.ofReal_one]
  calc
    ENNReal.ofReal (kappa * theta ^ 9 * r ^ 3) =
        ENNReal.ofReal (theta ^ 3) * ENNReal.ofReal (kappa * q ^ 3) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg htheta.1.le 3)]
      congr 1
      dsimp only [q]
      ring
    _ ≤ ENNReal.ofReal (theta ^ 3) * (ENNReal.ofReal C ^ 3 *
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r)) :=
      mul_le_mul_right hbound _
    _ = _ := by rw [← mul_assoc, hcancel, one_mul]

end PoincareConjecture.Proofs.M47
