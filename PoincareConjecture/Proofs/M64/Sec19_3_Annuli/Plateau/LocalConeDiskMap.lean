import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeRectangle
import PoincareConjecture.Proofs.M58.Cor18_28_DiskExtension
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularAngles

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

open Proofs.M58

def m64LocalConeDiskMap {Y : Type*} (H : ℝ × (Y × Y) → Y)
    (center : Y) (gamma : ℝ → Y) (z : LoopPlane) : Y := by
  classical
  exact if z = 0 then center else
    H (1 - diskTimeProfile ‖z‖, center, gamma (m60PlaneAngle z))

theorem m64_periodic_curve_planeAngle_eq {Y : Type*} {gamma : ℝ → Y}
    (hperiod : Function.Periodic gamma curvePeriod) {z : LoopPlane} (hz : z ≠ 0)
    {theta : ℝ} (hpolar : ‖z‖ • angularPoint theta = z) :
    gamma (m60PlaneAngle z) = gamma theta := by
  apply m60Periodic_eq_of_angularPoint_eq hperiod
  have h := congrArg (fun w : LoopPlane => ‖z‖⁻¹ • w)
    ((m60PlaneAngle_polar z).trans hpolar.symm)
  simpa only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul] using h

theorem m64LocalConeDiskMap_inner {Y : Type*} (H : ℝ × (Y × Y) → Y)
    (center : Y) (gamma : ℝ → Y) (h0 : ∀ x, H (0, center, gamma x) = center)
    {z : LoopPlane} (hz : ‖z‖ ≤ 1 / 2) : m64LocalConeDiskMap H center gamma z = center := by
  classical
  by_cases hz0 : z = 0
  · simp only [m64LocalConeDiskMap, if_pos hz0]
  · rw [m64LocalConeDiskMap, if_neg hz0,
      diskTimeProfile_eq_one (norm_nonneg z) hz, sub_self, h0]

theorem m64LocalConeDiskMap_polar {Y : Type*} (H : ℝ × (Y × Y) → Y)
    (center : Y) (gamma : ℝ → Y) (hperiod : Function.Periodic gamma curvePeriod)
    {r : ℝ} (hr : 0 < r) (theta : ℝ) :
    m64LocalConeDiskMap H center gamma (r • angularPoint theta) =
      H (1 - diskTimeProfile r, center, gamma theta) := by
  classical
  have hn : ‖r • angularPoint theta‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_angularPoint, mul_one]
  have hz : r • angularPoint theta ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact hr)
  rw [m64LocalConeDiskMap, if_neg hz,
    m64_periodic_curve_planeAngle_eq hperiod hz (by rw [hn]), hn]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in

theorem m64LocalConeDiskMap_contMDiff
    (H : ℝ × (M × M) → M) (center : M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hperiod : Function.Periodic gamma curvePeriod)
    (h0 : ∀ x, H (0, center, gamma x) = center)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 H
        (t, center, gamma x)) :
    ContMDiff (𝓡 2) (𝓡 n) 1 (m64LocalConeDiskMap H center gamma) := by
  classical
  intro z
  by_cases hz : z = 0
  · subst z
    have hc : ContMDiffAt (𝓡 2) (𝓡 n) 1 (fun _ : LoopPlane => center) 0 :=
      contMDiffAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : LoopPlane)
      (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    exact m64LocalConeDiskMap_inner H center gamma h0 (mem_ball_zero_iff.mp hw).le
  · obtain ⟨theta, htheta, hpolar⟩ := m60_exists_contDiffAt_planeAngle hz
    have htime : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1
        (fun w : LoopPlane => 1 - diskTimeProfile ‖w‖) z :=
      ((contDiffAt_const.sub (contDiff_diskTimeProfile.contDiffAt.comp z
        (contDiffAt_norm ℝ hz))).of_le (by simp)).contMDiffAt
    have ht : 1 - diskTimeProfile ‖z‖ ∈ Icc (0 : ℝ) 1 := by
      obtain ⟨hlo, hhi⟩ := diskTimeProfile_mem_Icc ‖z‖
      constructor <;> linarith
    have hmain := (hH _ ht (theta z)).comp z (htime.prodMk
      (contMDiffAt_const.prodMk (hgamma.contMDiffAt.comp z htheta.contMDiffAt)))
    apply hmain.congr_of_eventuallyEq
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := hw
    rw [m64LocalConeDiskMap, if_neg hw0,
      m64_periodic_curve_planeAngle_eq hperiod hw0 (hpolar w)]
    rfl

theorem m64LocalConeDiskMap_boundary {Y : Type*}
    (H : ℝ × (Y × Y) → Y) (center : Y) (gamma : ℝ → Y)
    (hperiod : Function.Periodic gamma curvePeriod)
    (h1 : ∀ x, H (1, center, gamma x) = gamma x) (x : ℝ) :
    m64LocalConeDiskMap H center gamma (angularPoint x) = gamma x := by
  have h := m64LocalConeDiskMap_polar H center gamma hperiod (r := 1) zero_lt_one x
  simpa only [one_smul, diskTimeProfile_one, sub_zero, h1] using h

end PoincareConjecture
