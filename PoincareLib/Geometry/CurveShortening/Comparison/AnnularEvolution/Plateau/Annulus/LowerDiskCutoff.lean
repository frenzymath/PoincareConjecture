import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.RadialGeometry
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.SobolevExtension

/-!
# A cutoff around the physical lower half-disk

Strict bounds on the center and radius place the full closed disk in
the reflected open strip. A smooth compact cutoff is identically one
on a neighborhood of every point of that disk. Source: Morrey ICM
pp. 181-185; M64 boundary semicircle assembly derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareMT

/-- The full disk centered on the lower face admits a genuine interior cutoff in the
reflected strip. Its neighborhood equality also fixes every derivative on the disk. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. M64 derivation
2026-09-26-boundary-semicircle-assembly.md. -/
theorem m64Annulus_lower_disk_cutoff {x H : ℝ}
    (hx : H < x) (hP : x + H < curvePeriod) (hH : H < 1) :
    ∃ chi : LoopPlane → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ m64AnnulusLowerDomain ∧
      ∀ z ∈ closedBall (0 : LoopPlane) H,
        chi =ᶠ[𝓝 (z + annulusPoint x 0)] (fun _ => (1 : ℝ)) := by
  let a := annulusPoint x 0
  let K := closedBall a H
  have hKO : K ⊆ m64AnnulusLowerDomain := by
    intro p hp
    have hb (i : Fin 2) : |(p - a) i| ≤ H :=
      (PiLp.norm_apply_le (p - a) i).trans (mem_closedBall_iff_norm.mp hp)
    have h0 : |p 0 - x| ≤ H := by simpa [a, annulusPoint] using hb 0
    have h1 : |p 1| ≤ H := by simpa [a, annulusPoint] using hb 1
    obtain ⟨h0l, h0r⟩ := abs_le.mp h0
    obtain ⟨h1l, h1r⟩ := abs_le.mp h1
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨delta, chi, hd, _, hchi, hc, _, hone, hs⟩ :=
    Poincare.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (isCompact_closedBall a H) m64AnnulusLowerDomain_isOpen hKO
  refine ⟨chi, hchi, hc, hs, ?_⟩
  intro z hz
  have hp : z + a ∈ K := by
    simpa only [K, mem_closedBall_iff_norm, add_sub_cancel_right]
      using mem_closedBall_zero_iff.mp hz
  filter_upwards [ball_mem_nhds (z + a) hd] with p hpball
  exact hone p (mem_cthickening_of_dist_le p (z + a) delta K hp
    (mem_ball.mp hpball).le)

end PoincareMT
