import PoincareConjecture.Proofs.M15.RawBallCylinder
import PoincareConjecture.Proofs.M12.GeneralizedCylinderRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

variable {F : GeneralizedRicciFlowData.{u}} (G : M12.FlowBoxRicciGeometry F)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)

include hM13

theorem raw_closed_noncollapse {T r r0 kappa : ℝ} (x : (F.slice T).carrier)
    (hN : M15GeneralizedNoncollapseAt G.toLGeometry (⟨T, x⟩ : F.point) r0 kappa)
    (hr : 0 < r) (hle : r ≤ r0)
    (e : GeneralizedFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
      ((F.metric T).ball x r))
    (hI : Icc (T - r ^ 2) T ⊆ F.interval)
    (hbase : ∀ h y, y ∈ (F.metric T).ball x r →
      e.pointMap 0 h y = (⟨T, y⟩ : F.point))
    (hcurv : ∀ s hs y, y ∈ (F.metric T).ball x r →
      F.curvatureNorm (e.pointMap s hs y) ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (kappa * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  have h := hN r hr hle ((G.sliceIdentification T).identification x)
    ((G.sliceIdentification T).identification_eq x) _ (rawBallSource F T x r)
    (rawActualBallCylinder G hM13 x hr e hI hbase hcurv)
  have hball := M13.originalSlice_ball G hM13 T x r
  have hvol := M13.originalSlice_volume G hM13 T ((F.metric T).ball x r)
  change ENNReal.ofReal (kappa * r ^ 3) ≤
    calibratedMetricVolume (G.realization.slices T).metricOnPoints
      ((G.realization.slices T).metricOnPoints.ball
        ((G.sliceIdentification T).identification x) r) at h
  rw [← hball, hvol] at h
  exact h

theorem raw_noncollapse {p : F.point} {r0 kappa : ℝ}
    (hN : M15GeneralizedNoncollapseAt G.toLGeometry p r0 kappa) :
    GeneralizedKappaNoncollapsedAt F p kappa r0 := by
  rcases p with ⟨T, x⟩
  intro r hr hle hI e hbase hcurv
  have hsmall (rho : ℝ) (hrho : rho ∈ Ioo 0 r) :
      ENNReal.ofReal (kappa * rho ^ 3) ≤
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
    have hsq : rho ^ 2 < r ^ 2 := by nlinarith [hrho.1, hrho.2]
    have hJ : Icc (-rho ^ 2) 0 ⊆ Ioc (-r ^ 2) 0 := by
      intro s hs
      exact ⟨by linarith [hs.1], hs.2⟩
    have hU : (F.metric T).ball x rho ⊆ (F.metric T).ball x r := by
      intro y hy
      exact lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hrho.2.le)
    have htime : Icc (T - rho ^ 2) T ⊆ F.interval := by
      intro t ht
      exact hI ⟨by linarith [ht.1], ht.2⟩
    have hscale : r⁻¹ ^ 2 ≤ rho⁻¹ ^ 2 := by
      gcongr <;> linarith [hrho.1, hrho.2]
    have h := raw_closed_noncollapse G hM13 x hN hrho.1 (hrho.2.le.trans hle)
      (e.restrict hJ hU) htime
      (fun h y hy => hbase (hJ h) y (hU hy))
      (fun s hs y hy => (le_abs_self _).trans ((hcurv s (hJ hs) y (hU hy)).trans hscale))
    exact h.trans (measure_mono hU)
  have hlim : Tendsto (fun rho : ℝ => ENNReal.ofReal (kappa * rho ^ 3)) (𝓝[<] r)
      (𝓝 (ENNReal.ofReal (kappa * r ^ 3))) :=
    ENNReal.tendsto_ofReal
      ((continuous_const.mul (continuous_id.pow 3)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  apply le_of_tendsto hlim
  have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] r := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hr)
  filter_upwards [self_mem_nhdsWithin, hpos] with rho hlt hpos'
  exact hsmall rho ⟨hpos', hlt⟩

end PoincareConjecture.Proofs.M15
