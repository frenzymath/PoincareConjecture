import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeTarget
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConePhaseGreen














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64BoundaryCone

open Proofs.M58

local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ





theorem exists_target_phase_halfCone {n m N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin m)) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    {P : EuclideanSpace ℝ (Fin N) → M} {beta : EuclideanSpace ℝ (Fin N) → ℝ}
    {v d : ℝ → EuclideanSpace ℝ (Fin N)} {gamma trace : ℝ → M}
    {L bTrace : ℝ → ℝ} {r rho k K : ℝ}
    (hr : 0 < r) (hrho : 0 < rho) (hk : k ≠ 0) (hK : 0 ≤ K)
    (hP : ContMDiffOn (𝓡 N) (𝓡 n) 1 P (ball 0 (2 * rho)))
    (hbeta : ContDiffOn ℝ 1 beta (ball 0 (2 * rho)))
    (hPobs : ∀ y ∈ closedBall 0 rho, R (e (P y)) = angularPoint (k * beta y))
    (hD : ∀ y ∈ closedBall 0 rho, ‖fderiv ℝ (e ∘ P) y‖ ≤ K)
    (hv : AbsolutelyContinuousOnInterval v 0 Real.pi)
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 rho))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      v t - v s = ∫ theta in s..t, d theta)
    (hgamma : ∀ theta ∈ Icc (0 : ℝ) Real.pi, P (v theta) = gamma theta)
    (hL : ContinuousOn L (Icc (0 : ℝ) Real.pi))
    (hobs : ∀ theta ∈ Icc (0 : ℝ) Real.pi,
      R (e (gamma theta)) = angularPoint (k * L theta))
    (hdiam : ∀ s ∈ Icc (-r) r,
      P (halfConeDiameter r (v 0) (v Real.pi) s) = trace s)
    (hb : ContinuousOn bTrace (Icc (-r) r)) (hbr : bTrace r = L 0)
    (htraceobs : ∀ s ∈ Icc (-r) r, R (e (trace s)) = angularPoint (k * bTrace s)) :
    let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
    ∃ (f : LoopPlane → M) (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
      (u : LoopPlane → ℝ) (W : Fin 2 → LoopPlane → ℝ),
      MemLp (e ∘ f) 2 (volume.restrict S) ∧
      (∀ i, MemLp (V i) 2 (volume.restrict S)) ∧
      MemLp u 2 (volume.restrict S) ∧ (∀ i, MemLp (W i) 2 (volume.restrict S)) ∧
      (∀ i, ∀ z ∈ S, V i z ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f z))) ∧
      (∀ z ∈ S, R (e (f z)) = angularPoint (k * u z)) ∧
      (∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ (i : Fin 2) (j : Fin m),
        (∫ z in S, V i z j * test z + e (f z) j * fderiv ℝ test z (basis i)) =
          r * (∫ theta in (0 : ℝ)..Real.pi,
            e (gamma theta) j * test (r • angularPoint theta) * angularPoint theta i) -
          (basis 1) i * ∫ s in (-r)..r, e (trace s) j * test (s • basis 0)) ∧
      (∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ i : Fin 2,
        (∫ z in S, W i z * test z + u z * fderiv ℝ test z (basis i)) =
          r * (∫ theta in (0 : ℝ)..Real.pi,
            L theta * test (r • angularPoint theta) * angularPoint theta i) -
          (basis 1) i * ∫ s in (-r)..r, bTrace s * test (s • basis 0)) ∧
      (∫ z in S, ∑ i : Fin 2, ‖V i z‖ ^ 2) ≤
        (K ^ 2 / 2) * (1 + 4 * Real.pi ^ 2) *
          ∫ theta in Icc (0 : ℝ) Real.pi, ‖d theta‖ ^ 2 := by
  let center := (1 / 2 : ℝ) • (v 0 + v Real.pi)
  let f := coneDiskMap P r center v 0
  let V := coneDiskField (e ∘ P) r center v d 0
  let B := normalizedPhase beta v L
  let u := coneDiskMap B r center v 0
  let W := coneDiskField B r center v d 0
  have hvc : ContinuousOn v (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hv.continuousOn
  have h0 : center ∈ closedBall 0 rho := midpoint_mem_closedBall
    (hvb ⟨le_rfl, Real.pi_pos.le⟩) (hvb ⟨Real.pi_pos.le, le_rfl⟩)
  have hg : ContDiffOn ℝ 1 (e ∘ P) (ball 0 (2 * rho)) :=
    contMDiffOn_iff_contDiffOn.mp (he.comp_contMDiffOn hP)
  obtain ⟨hf, hV⟩ := halfCone_memLp hr hrho hK hvc hg h0 hvb hd hD (0 : LoopPlane)
  have harc (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) Real.pi) :
      angularPoint (k * L theta) = angularPoint (k * beta (v theta)) := by
    rw [← hPobs _ (hvb htheta), hgamma theta htheta]
    exact (hobs theta htheta).symm
  have hdiamobs (s : ℝ) (hs : s ∈ Icc (-r) r) :
      angularPoint (k * beta (halfConeDiameter r (v 0) (v Real.pi) s)) =
        angularPoint (k * bTrace s) := by
    have hm : halfConeDiameter r (v 0) (v Real.pi) s ∈ closedBall 0 rho := by
      apply (convex_closedBall (0 : EuclideanSpace ℝ (Fin N)) rho).mapsTo_lineMap
        (hvb ⟨Real.pi_pos.le, le_rfl⟩) (hvb ⟨le_rfl, Real.pi_pos.le⟩)
      exact ⟨div_nonneg (by linarith [hs.1]) (by positivity),
        (div_le_one (by positivity : 0 < 2 * r)).mpr (by linarith [hs.2])⟩
    rw [← hPobs _ hm, hdiam s hs]
    exact htraceobs s hs
  obtain ⟨hu, hW, huobs, hgreenPhase⟩ := normalizedPhase_halfCone_green
    hr hrho hk hbeta hv hvb hd hinc hL harc bTrace hb hbr hdiamobs
  refine ⟨f, V, u, W, hf, hV, hu, hW, ?_, ?_, ?_, hgreenPhase, ?_⟩
  · intro i z hz
    exact coneDiskField_tangent hr hrho he hP h0 hvb hz i
  · intro z hz
    exact (coneDiskMap_observation hr h0 hvb hPobs hz).trans (huobs z).symm
  · intro test htest i j
    calc
      _ = r * (∫ theta in (0 : ℝ)..Real.pi,
          e (P (v theta)) j * test (r • angularPoint theta) * angularPoint theta i) -
          (basis 1) i * ∫ s in (-r)..r,
            e (P (halfConeDiameter r (v 0) (v Real.pi) s)) j * test (s • basis 0) :=
        midpoint_halfCone_green_clm hr hrho hK hv hg hvb hd hinc hD test htest i j
      _ = _ := by
        congr 1
        · congr 1
          apply intervalIntegral.integral_congr
          intro theta htheta
          dsimp only
          rw [hgamma theta (by simpa only [uIcc_of_le Real.pi_pos.le] using htheta)]
        · congr 1
          apply intervalIntegral.integral_congr
          intro s hs
          dsimp only
          rw [hdiam s (by simpa only [uIcc_of_le (by linarith : -r ≤ r)] using hs)]
  · exact (midpoint_halfCone_derivativeEnergy_le hr hrho hK hvc hg hvb hd hinc hD).2

end PoincareConjecture.M64BoundaryCone
