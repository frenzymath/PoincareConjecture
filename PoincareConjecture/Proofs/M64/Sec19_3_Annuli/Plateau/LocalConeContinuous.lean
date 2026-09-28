import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeDiskMap












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {M : Type*} [TopologicalSpace M]



theorem m64LocalConeDiskMap_continuous
    (H : ℝ × (M × M) → M) (center : M) (gamma : ℝ → M)
    (hgamma : Continuous gamma) (hperiod : Function.Periodic gamma curvePeriod)
    (h0 : ∀ x, H (0, center, gamma x) = center)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ContinuousAt H (t, center, gamma x)) :
    Continuous (m64LocalConeDiskMap H center gamma) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    have hc : ContinuousAt (fun _ : LoopPlane => center) 0 := continuousAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : LoopPlane)
      (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    exact m64LocalConeDiskMap_inner H center gamma h0 (mem_ball_zero_iff.mp hw).le
  · obtain ⟨theta, htheta, hpolar⟩ := m60_exists_contDiffAt_planeAngle hz
    have htime : ContinuousAt (fun w : LoopPlane => 1 - diskTimeProfile ‖w‖) z :=
      continuousAt_const.sub (contDiff_diskTimeProfile.continuous.continuousAt.comp
        continuous_norm.continuousAt)
    have ht : 1 - diskTimeProfile ‖z‖ ∈ Icc (0 : ℝ) 1 := by
      obtain ⟨hlo, hhi⟩ := diskTimeProfile_mem_Icc ‖z‖
      constructor <;> linarith
    have harg : ContinuousAt (fun w : LoopPlane =>
        (1 - diskTimeProfile ‖w‖, center, gamma (theta w))) z :=
      htime.prodMk (continuousAt_const.prodMk
        (hgamma.continuousAt.comp htheta.continuousAt))
    have hc : ContinuousAt (fun w : LoopPlane =>
        H (1 - diskTimeProfile ‖w‖, center, gamma (theta w))) z :=
      (hH _ ht (theta z)).comp
        (f := fun w : LoopPlane => (1 - diskTimeProfile ‖w‖, center, gamma (theta w))) harg
    apply hc.congr_of_eventuallyEq
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := hw
    rw [m64LocalConeDiskMap, if_neg hw0,
      m64_periodic_curve_planeAngle_eq hperiod hw0 (hpolar w)]



theorem m64LocalConeDiskMap_tendsto
    (H : ℝ × (M × M) → M) (center : ℕ → M) (gamma : ℕ → ℝ → M)
    (c : M) (u : ℝ → M) (hc : Tendsto center atTop (𝓝 c))
    (hu : ∀ x, Tendsto (fun j => gamma j x) atTop (𝓝 (u x)))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ContinuousAt H (t, c, u x))
    (z : LoopPlane) :
    Tendsto (fun j => m64LocalConeDiskMap H (center j) (gamma j) z) atTop
      (𝓝 (m64LocalConeDiskMap H c u z)) := by
  classical
  by_cases hz : z = 0
  · simpa only [m64LocalConeDiskMap, if_pos hz] using hc
  · have ht : 1 - diskTimeProfile ‖z‖ ∈ Icc (0 : ℝ) 1 := by
      obtain ⟨hlo, hhi⟩ := diskTimeProfile_mem_Icc ‖z‖
      constructor <;> linarith
    have harg : Tendsto (fun j =>
        (1 - diskTimeProfile ‖z‖, center j, gamma j (m60PlaneAngle z))) atTop
        (𝓝 (1 - diskTimeProfile ‖z‖, c, u (m60PlaneAngle z))) :=
      tendsto_const_nhds.prodMk_nhds (hc.prodMk_nhds (hu (m60PlaneAngle z)))
    have hlim := (hH _ ht (m60PlaneAngle z)).tendsto.comp harg
    simpa only [m64LocalConeDiskMap, if_neg hz, Function.comp_def] using hlim

end PoincareConjecture
