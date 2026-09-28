import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryCollar

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace M65Gauss

theorem halfDisk_actual_frame_connection_log {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) R ∩ {z | 0 < z.im}))
    (hconf : ∀ z ∈ closedBall (0 : ℂ) R ∩ {w | 0 ≤ w.im},
      let L := fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (L 1) (L 1) = g.inner (H z) (L I) (L I) ∧
        g.inner (H z) (L 1) (L I) = 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R ∩ {w | 0 < w.im})
    (hunit :
      let V := normalizedResidualFrame (g.euclideanCoefficients (H z)) (halfDiskGradient H R z)
      g.inner (H z) V.1 V.1 = 1) :
    let V := fun w => normalizedResidualFrame (g.euclideanCoefficients (H w))
      (halfDiskGradient H R w)
    0 < g.inner (H z) (fderiv ℝ H z 1) (fderiv ℝ H z 1) ∧
    g.inner (H z) (covariantDerivativeAlongMap D H (fun w => (V w).1) z 1) (V z).2 =
      -fderiv ℝ (fun w => Real.log (g.inner (H w)
        (fderiv ℝ H w 1) (fderiv ℝ H w 1))) z I / 2 := by
  let U := ball (0 : ℂ) R ∩ {w | 0 < w.im}
  let V := fun w => normalizedResidualFrame (g.euclideanCoefficients (H w))
    (halfDiskGradient H R w)
  let F := fun w => normalizedResidualFrame (g.euclideanCoefficients (H w))
    (complexGradient H w)
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hVF : V =ᶠ[𝓝 z] F := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrArg (normalizedResidualFrame (g.euclideanCoefficients (H w)))
      (halfDisk_fields_eq D H hw).1
  have hpos : 0 < g.inner (H z) (fderiv ℝ H z 1) (fderiv ℝ H z 1) := by
    apply g.pos
    intro hzero
    have hVzero : (V z).1 = 0 := by
      rw [hVF.self_of_nhds]
      simp only [F, normalizedResidualFrame, (residual_columns_complexGradient H z).1,
        hzero, smul_zero]
    change g.inner (H z) (V z).1 (V z).1 = 1 at hunit
    rw [hVzero, map_zero] at hunit
    exact zero_ne_one hunit
  have hordinary : ∀ᶠ w in 𝓝 z,
      g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w 1) =
        g.inner (H w) (fderiv ℝ H w I) (fderiv ℝ H w I) ∧
      g.inner (H w) (fderiv ℝ H w 1) (fderiv ℝ H w I) = 0 := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simpa only [fderivWithin_of_mem_nhds (halfDisk_mem_nhds hw)] using
      hconf w ⟨ball_subset_closedBall hw.1, (show 0 < w.im from hw.2).le⟩
  have hconnection := normalized_gradient_connection_log D
    (hHi.contDiffAt (hU.mem_nhds hz)) hpos hordinary
  have hfirst : (fun w => (V w).1) =ᶠ[𝓝 z] fun w => (F w).1 :=
    hVF.mono (fun _ hw => congrArg Prod.fst hw)
  refine ⟨hpos, ?_⟩
  change g.inner (H z) (covariantDerivativeAlongMap D H (fun w => (V w).1) z 1)
    (V z).2 = _
  simpa only [covariantDerivativeAlongMap, hfirst.fderiv_eq,
    hVF.self_of_nhds] using hconnection

end PoincareConjecture.M64
