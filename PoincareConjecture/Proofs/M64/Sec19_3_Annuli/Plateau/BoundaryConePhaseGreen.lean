import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConePhase














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M64BoundaryCone

open Proofs.M58

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
  [CompleteSpace C] [ProperSpace C]






theorem normalizedPhase_halfCone_green {beta : C → ℝ} {v d : ℝ → C} {L : ℝ → ℝ}
    {r rho k : ℝ} (hr : 0 < r) (hrho : 0 < rho) (hk : k ≠ 0)
    (hbeta : ContDiffOn ℝ 1 beta (ball 0 (2 * rho)))
    (hv : AbsolutelyContinuousOnInterval v 0 Real.pi)
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 rho))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      v t - v s = ∫ theta in s..t, d theta)
    (hL : ContinuousOn L (Icc (0 : ℝ) Real.pi))
    (hobs : ∀ theta ∈ Icc (0 : ℝ) Real.pi,
      angularPoint (k * L theta) = angularPoint (k * beta (v theta)))
    (bTrace : ℝ → ℝ) (hb : ContinuousOn bTrace (Icc (-r) r))
    (hbr : bTrace r = L 0)
    (hdiameter : ∀ s ∈ Icc (-r) r,
      angularPoint (k * beta (halfConeDiameter r (v 0) (v Real.pi) s)) =
        angularPoint (k * bTrace s)) :
    let B := normalizedPhase beta v L
    let center := (1 / 2 : ℝ) • (v 0 + v Real.pi)
    let u := coneDiskMap B r center v 0
    let W := coneDiskField B r center v d 0
    let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
    MemLp u 2 (volume.restrict S) ∧ (∀ i, MemLp (W i) 2 (volume.restrict S)) ∧
      (∀ z, angularPoint (k * u z) =
        angularPoint (k * coneDiskMap beta r center v 0 z)) ∧
      ∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ i : Fin 2,
        (∫ z in S, W i z * test z + u z *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
          r * (∫ theta in (0 : ℝ)..Real.pi,
            L theta * test (r • angularPoint theta) * angularPoint theta i) -
          (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
            ∫ s in (-r)..r, bTrace s * test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  let B := normalizedPhase beta v L
  let center := (1 / 2 : ℝ) • (v 0 + v Real.pi)
  have hvc : ContinuousOn v (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hv.continuousOn
  have hclosed : closedBall (0 : C) rho ⊆ ball 0 (2 * rho) :=
    closedBall_subset_ball (by linarith)
  obtain ⟨hB, htrace, hBobservation⟩ := normalizedPhase_properties hk hbeta hvc
    (fun _ ht => hclosed (hvb ht)) hL hobs
  let chord := halfConeDiameter r (v 0) (v Real.pi)
  have hchord : Continuous chord := by
    change Continuous (fun s => halfConeDiameter r (v 0) (v Real.pi) s)
    simp only [halfConeDiameter, AffineMap.lineMap_apply_module]
    fun_prop
  have hchordBall : MapsTo chord (Icc (-r) r) (ball 0 (2 * rho)) := by
    intro s hs
    apply hclosed
    apply (convex_closedBall (0 : C) rho).mapsTo_lineMap
      (hvb ⟨Real.pi_pos.le, le_rfl⟩) (hvb ⟨le_rfl, Real.pi_pos.le⟩)
    exact ⟨div_nonneg (by linarith [hs.1]) (by positivity),
      (div_le_one (by positivity : 0 < 2 * r)).mpr (by linarith [hs.2])⟩
  have hright : chord r = v 0 := by
    have hratio : (r + r) / (2 * r) = 1 := by
      rw [← two_mul, div_self (mul_ne_zero (by norm_num) hr.ne')]
    simp only [chord, halfConeDiameter, hratio, AffineMap.lineMap_apply_one]
  have hbase : B (chord r) = bTrace r := by
    rw [hright, hbr]
    exact htrace 0 ⟨le_rfl, Real.pi_pos.le⟩
  have hdiam (s : ℝ) (hs : s ∈ Icc (-r) r) : B (chord s) = bTrace s := by
    have h := m64ContinuousPhase_difference isPreconnected_Icc hk
      (hB.continuousOn.comp hchord.continuousOn hchordBall) hb
      (fun t ht => (hBobservation (chord t)).trans (hdiameter t ht))
      (show r ∈ Icc (-r) r from ⟨by linarith, le_rfl⟩) s hs
    change B (chord s) = bTrace s + (B (chord r) - bTrace r) at h
    simpa only [hbase, sub_self, add_zero] using h
  have hDB : ContinuousOn (fderiv ℝ B) (closedBall 0 rho) :=
    (hB.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).mono hclosed
  obtain ⟨K0, hK0⟩ := (isCompact_closedBall (0 : C) rho).exists_bound_of_continuousOn hDB
  let K := max K0 0
  have hK : 0 ≤ K := le_max_right _ _
  have hD (y : C) (hy : y ∈ closedBall 0 rho) : ‖fderiv ℝ B y‖ ≤ K :=
    (hK0 y hy).trans (le_max_left _ _)
  have h0 : center ∈ closedBall 0 rho := midpoint_mem_closedBall
    (hvb ⟨le_rfl, Real.pi_pos.le⟩) (hvb ⟨Real.pi_pos.le, le_rfl⟩)
  obtain ⟨hu, hW⟩ := halfCone_memLp hr hrho hK hvc hB h0 hvb hd hD (0 : LoopPlane)
  refine ⟨hu, hW, fun z => hBobservation _, ?_⟩
  intro test htest i
  rw [(midpoint_halfCone_green hr hrho hK hv hB hvb hd hinc hD test htest i).2]
  congr 1
  · congr 1
    apply intervalIntegral.integral_congr
    intro theta htheta
    dsimp only
    rw [htrace theta (by simpa only [uIcc_of_le Real.pi_pos.le] using htheta)]
  · congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    exact congrArg (fun t => t * test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (hdiam s (by simpa only [uIcc_of_le (by linarith : -r ≤ r)] using hs))

end PoincareConjecture.M64BoundaryCone
