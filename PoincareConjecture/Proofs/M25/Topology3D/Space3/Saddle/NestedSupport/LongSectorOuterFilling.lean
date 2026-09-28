import PoincareConjecture.Proofs.M25.Topology3D.Gluing.RaisedReturnBoundaryAvoidance
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorOuterGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorOuterSide

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem saddle_nested_raised_long_return_outer_filling
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h nu : ℝ) (hh : 0 < h) (hhnu : h < nu / 128)
    (hsmall : h < 1 / 1024) (inner : Fin 2) :
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let outer : Fin 2 := raisedReturnOther inner
    let gamma : ℝ → E2 := raisedReturnPhysicalCurve kappa J2 h inner
    ∀ (alpha : ℝ → E2) (Bi Bo : BallNeighborhoodChart E2 E2) (Eta : Set E2),
      InjOn alpha (Ioo (-nu) (1 + nu)) →
      (∀ t, |t| < nu → alpha t = kappa ((1 + t) • port (ep (outer, 0)))) →
      (∀ t, |t - 1| < nu → alpha t = kappa ((2 - t) • port (ep (outer, 1)))) →
      Bo.boundary = alpha '' Icc (0 : ℝ) 1 ∪ Eta →
      Eta ⊆ kappa '' closedBall (0 : E2) 1 →
      (alpha '' Icc (0 : ℝ) 1) ∩
          (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) =
        kappa ''
          (((fun r : ℝ => r • port (ep (outer, 0))) '' Icc 1 (1 + 32 * h)) ∪
          ((fun r : ℝ => r • port (ep (outer, 1))) '' Icc 1 (1 + 32 * h))) →
      kappa '' {x : E2 |
        1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧
          |(J2 x).1| < raisedReturnSign inner * (J2 x).2} ⊆ Bi.inside →
      Bi.closedRegion ⊆ Bo.inside →
      (gamma '' Ioo h (1 - h) ⊆ Bo.inside) ∧
        (gamma '' Icc (0 : ℝ) 1 ⊆ Bo.closedRegion) ∧
        (gamma '' Icc (0 : ℝ) 1) ∩ (alpha '' Icc (3 * h) (1 - 3 * h)) =
          {alpha (3 * h), alpha (1 - 3 * h)} := by
  dsimp only
  intro alpha Bi Bo Eta hAlphaInj hInitial hTerminal hBoundary hEta hAnnular hInside hNested
  have hactive := saddle_nested_raised_return_active_geometry
    kappa hkappaSource J2 hJ2 h hh hsmall inner
  have hmid := saddle_nested_raised_long_return_midpoint_inside
    kappa J2 hJ2 h hh hsmall inner Bi Bo hInside hNested
  have hgerms := saddle_nested_raised_long_return_original_germs
    kappa J2 h nu hh hhnu hsmall inner alpha hInitial hTerminal
  have hnu : 0 < nu := by linarith
  have h01old : Icc (0 : ℝ) 1 ⊆ Ioo (-nu) (1 + nu) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hAlpha01 : InjOn alpha (Icc (0 : ℝ) 1) := hAlphaInj.mono h01old
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      raisedReturnPlanarCurve J2 h inner t ∈ kappa.source := by
    apply hkappaSource
    rw [mem_closedBall_zero_iff,
      raisedReturnPlanar_norm_eq_radius J2 hJ2 h inner t
        (raisedReturnRadius_nonneg h hh t)]
    have hb := raisedReturnRadius_upper_closed h hh hsmall t ht
    linarith
  have hcont : ContinuousOn (raisedReturnPhysicalCurve kappa J2 h inner)
      (Icc (0 : ℝ) 1) :=
    kappa.continuousOn.comp (raisedReturnPlanar_contDiff J2 h inner).continuous.continuousOn
      hsource
  obtain ⟨hactiveInside, hclosed, hmeet⟩ :=
    saddle_nested_raised_long_return_outer_closed kappa Bo alpha
      (raisedReturnPhysicalCurve kappa J2 h inner) Eta _ h (3 * h) (1 - 3 * h)
      hh (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) hBoundary hEta hAnnular
      hactive.1 hactive.2.1 hactive.2.2.1 hactive.2.2.2 hcont hmid
      hgerms.2.2.1 hgerms.2.2.2 hAlpha01
  refine ⟨hactiveInside, hclosed, ?_⟩
  have h0 : raisedReturnPhysicalCurve kappa J2 h inner 0 = alpha (1 - 3 * h) := by
    simpa only [add_zero] using hgerms.2.2.1 0 ⟨le_rfl, hh.le⟩
  have h1 : raisedReturnPhysicalCurve kappa J2 h inner 1 = alpha (3 * h) := by
    simpa only [add_sub_cancel_right] using hgerms.2.2.2 1 ⟨by linarith, le_rfl⟩
  rw [hmeet, h0, h1, Set.pair_comm]

end PoincareConjecture.M25.Topology3D
