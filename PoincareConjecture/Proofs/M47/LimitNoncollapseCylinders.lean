import PoincareConjecture.Proofs.M47.LimitNoncollapseRecenter
import PoincareConjecture.Proofs.M12.GeneralizedCylinderRestriction











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem limitNoncollapse_shrunk_closed_time_subset {t r rho : ℝ}
    (hrho : 0 < rho) (hsmall : rho < r) :
    Icc (t - rho ^ 2) t ⊆ Ioc (t - r ^ 2) t := by
  have hsq : rho ^ 2 < r ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hsmall) (add_pos (hrho.trans hsmall) hrho)]
  intro s hs
  exact ⟨by linarith [hs.1], hs.2⟩


theorem limitNoncollapse_physical_radius_sq {scale : ℝ} (hscale : 0 < scale)
    (rho : ℝ) : scale * (rho / Real.sqrt scale) ^ 2 = rho ^ 2 := by
  rw [div_pow, Real.sq_sqrt hscale.le]
  field_simp



theorem limitNoncollapse_physical_time_range {scale : ℝ} (hscale : 0 < scale)
    (a rho : ℝ) :
    MapsTo (fun s => a + scale * s) (Icc (-(rho / Real.sqrt scale) ^ 2) 0)
      (Icc (a - rho ^ 2) a) := by
  intro s hs
  have hlo := mul_le_mul_of_nonneg_left hs.1 hscale.le
  have hhi := mul_le_mul_of_nonneg_left hs.2 hscale.le
  have hsq := limitNoncollapse_physical_radius_sq hscale rho
  constructor <;> nlinarith



theorem limitNoncollapse_physical_curvature_threshold {scale : ℝ}
    (hscale : 0 < scale) (rho : ℝ) :
    scale * rho⁻¹ ^ 2 = (rho / Real.sqrt scale)⁻¹ ^ 2 := by
  rw [inv_div, div_eq_mul_inv, mul_pow, Real.sq_sqrt hscale.le]



theorem limitNoncollapse_physical_curvature_bound {scale rho K : ℝ}
    (hscale : 0 < scale) (hK : |K| / scale ≤ rho⁻¹ ^ 2) :
    |K| ≤ (rho / Real.sqrt scale)⁻¹ ^ 2 := by
  rw [← limitNoncollapse_physical_curvature_threshold hscale]
  have h := (div_le_iff₀ hscale).mp hK
  nlinarith

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}





theorem limitNoncollapse_volume_of_recentered_test
    (e : GeneralizedFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (a : ℝ) (ha : a ∈ I) (p : (F.slice (origin + a / scale)).carrier)
    {r kappa r0 : ℝ} (hr : 0 < r) (hr0 : r ≤ r0)
    (hnc : GeneralizedKappaNoncollapsedAt F (⟨origin + a / scale, p⟩ : F.point)
      kappa r0)
    (hrange : MapsTo (fun s => a + scale * s) (Icc (-r ^ 2) 0) I)
    (hball : (F.metric (origin + a / scale)).ball p r ⊆ e.forward a ha '' U)
    (hK : ∀ s (hs : s ∈ Icc (-r ^ 2) 0),
      ∀ x ∈ (F.metric (origin + a / scale)).ball p r,
        |F.curvatureNorm (e.pointMap (a + scale * s) (hrange hs)
          (e.inverse a ha x))| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (kappa * r ^ 3) ≤ calibratedMetricVolume
      (F.metric (origin + a / scale)) ((F.metric (origin + a / scale)).ball p r) := by
  let V := (F.metric (origin + a / scale)).ball p r
  let d := limitNoncollapseCylinderRecenter e hU a ha hrange V hball
  have htime : Ioc ((origin + a / scale) - r ^ 2) (origin + a / scale) ⊆
      F.interval := by
    intro t ht
    have hs : t - (origin + a / scale) ∈ Icc (-r ^ 2) 0 :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h := limitNoncollapseCylinder_time_mem d _ hs p
    simpa only [div_one, add_sub_cancel] using h
  let dOpen := d.restrict Ioc_subset_Icc_self (Subset.rfl : V ⊆ V)
  apply hnc r hr hr0 htime dOpen
  · intro h0 x hx
    exact limitNoncollapseCylinderRecenter_zero e hU a ha hrange V hball
      (Ioc_subset_Icc_self h0) x hx
  · intro s hs x hx
    change |F.curvatureNorm (d.pointMap s (Ioc_subset_Icc_self hs) x)| ≤ r⁻¹ ^ 2
    rw [limitNoncollapseCylinderRecenter_curvatureNorm]
    exact hK s (Ioc_subset_Icc_self hs) x hx

end PoincareConjecture.M47
