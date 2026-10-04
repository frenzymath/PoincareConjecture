import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Modulus.FreeBoundaryTransport

/-!
# Actual C1 collars with exactly preserved annulus area

Constant radial collars have scalar rank and zero area. Two actual
annulus joins place the original Lipschitz seed between these collars.
Thus C1 boundary traces give C1 neighborhoods of both radial edges without
any area cost or regularity assumption on the original interior map.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareMT.M64Uniformization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Two zero-area constant radial collars preserve the annulus area and give genuine C1
neighborhoods of both boundary curves. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem scalarAnnulus_exists_flat_collars
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1) :
    ∃ B : M64Annulus g c0 c1, B.area = A.area ∧
      (∀ p : LoopPlane, p 1 ≤ (1 / 4 : ℝ) → B.map p = c0 (p 0)) ∧
      (∀ p : LoopPlane, (1 / 2 : ℝ) < p 1 → B.map p = c1 (p 0)) ∧
      ∀ p : LoopPlane, p 1 < (1 / 4 : ℝ) ∨ (1 / 2 : ℝ) < p 1 →
        ContMDiffAt (𝓡 2) (𝓡 n) 1 B.map p := by
  have hperiod0 : Function.Periodic c0 curvePeriod := by
    intro x
    rw [← A.lower_boundary, A.periodic, A.lower_boundary]
  have hperiod1 : Function.Periodic c1 curvePeriod := by
    intro x
    rw [← A.upper_boundary, A.periodic, A.upper_boundary]
  have hconstant (c : ℝ → M) (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c)
      (hperiod : Function.Periodic c curvePeriod) :
      ∃ C : M64Annulus g c c, C.map = (fun p : LoopPlane => c (p 0)) ∧ C.area = 0 := by
    obtain ⟨C, hmap, harea⟩ := m64_zero_area_boundary_collar g c id hc.continuous hperiod
      (m64PeriodicC1Curve_metric_lipschitz g hc hperiod) continuous_id
      (fun _ => rfl) ⟨1, by norm_num, fun _ _ => by simp⟩
    refine ⟨C, ?_, harea⟩
    rw [hmap]
    funext p
    congr 1
    dsimp only [id]
    ring
  obtain ⟨L, hL, hLA⟩ := hconstant c0 hc0 hperiod0
  obtain ⟨R, hR, hRA⟩ := hconstant c1 hc1 hperiod1
  obtain ⟨D, hD, hDA⟩ := m64Annulus_join_with_area L A
  obtain ⟨B, hB, hBA⟩ := m64Annulus_join_with_area D R
  have hlower (p : LoopPlane) (hp : p 1 ≤ (1 / 4 : ℝ)) : B.map p = c0 (p 0) := by
    rw [hB, m64AnnulusJoinMap, if_pos (by linarith), hD, m64AnnulusJoinMap]
    have hp' : (m64RadialDouble 0 p) 1 ≤ (1 / 2 : ℝ) := by
      change 2 * p 1 - 0 ≤ 1 / 2
      linarith
    rw [if_pos hp', hL]
    rfl
  have hupper (p : LoopPlane) (hp : (1 / 2 : ℝ) < p 1) : B.map p = c1 (p 0) := by
    rw [hB, m64AnnulusJoinMap, if_neg (not_le_of_gt hp), hR]
    rfl
  refine ⟨B, by rw [hBA, hDA, hLA, hRA]; simp, hlower, hupper, ?_⟩
  intro p hp
  have hproj : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 1 (fun q : LoopPlane => q 0) :=
    contMDiff_iff_contDiff.mpr (show LoopPlane →L[ℝ] ℝ from EuclideanSpace.proj 0).contDiff
  rcases hp with hp | hp
  · apply (hc0.comp hproj).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt (EuclideanSpace.proj 1).continuous
      continuous_const).mem_nhds hp] with q hq
    exact hlower q hq.le
  · apply (hc1.comp hproj).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const
      (EuclideanSpace.proj 1).continuous).mem_nhds hp] with q hq
    exact hupper q hq

end PoincareMT.M64Uniformization
