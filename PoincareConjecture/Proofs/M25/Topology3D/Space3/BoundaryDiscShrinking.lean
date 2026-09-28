import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRadialTracks

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_boundaryDisc_shrinking_isotopy (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ)) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      (∀ y, Φ 0 y = y) ∧
      (∀ t y, ‖Φ t y‖ = ‖y‖) ∧
      (∀ x ∈ closedBall 0 1, ∀ t : ℝ, 0 ≤ t →
        Φ t (stereoInvFun hv (D.chart x) : E) =
          (stereoInvFun hv (D.chart (Real.exp (-t) • x)) : E)) ∧
      (∀ U : Set E, IsOpen U → (stereoInvFun hv (D.chart 0) : E) ∈ U →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
          MapsTo (Φ t) ((fun x => (stereoInvFun hv x : E)) '' D.closedRegion) U) ∧
      ∃ C : Set E, IsCompact C ∧ C ⊆ radialStereoTarget v ∧
        ∀ t y, y ∉ C → Φ t y = y := by
  obtain ⟨W, hW, hWc, _, hag⟩ := exists_ball_radial_field D
  obtain ⟨k, l, hk, hl⟩ := compactField_bounds W hW hWc
  obtain ⟨Φ, hΦ, hzero, hnorm, htrack, C, hC, hCt, hfix⟩ :=
    exists_boundaryDisc_ambient_flow v hv W hW hWc hk hl
  have hrad (x : (ℝ ∙ v)ᗮ) (hx : x ∈ closedBall 0 1) (t : ℝ) (ht : 0 ≤ t) :
      Φ t (stereoInvFun hv (D.chart x) : E) =
        (stereoInvFun hv (D.chart (Real.exp (-t) • x)) : E) := by
    rw [htrack, boundedFlow_eq_chart_radial D W hk hl hag hx ht]
  refine ⟨Φ, hΦ, hzero, hnorm, hrad, ?_, C, hC, hCt, hfix⟩
  intro U hU hcenter
  have h0s : (0 : (ℝ ∙ v)ᗮ) ∈ D.chart.source :=
    D.closedBall_subset_source (mem_closedBall_self zero_le_one)
  have hdisc : ContinuousAt
      (fun x : (ℝ ∙ v)ᗮ => (stereoInvFun hv (D.chart x) : E)) 0 :=
    (continuous_subtype_val.comp (continuous_stereoInvFun hv)).continuousAt.comp
      (D.chart.continuousOn.continuousAt (D.chart.open_source.mem_nhds h0s))
  obtain ⟨eps, heps, hepsU⟩ :=
    Metric.mem_nhds_iff.mp (hdisc.preimage_mem_nhds (hU.mem_nhds hcenter))
  have hsmall : ∀ᶠ t : ℝ in atTop, Real.exp (-t) < eps :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds heps)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hsmall
  refine ⟨max 0 T, le_max_left _ _, ?_⟩
  intro t ht y hy
  obtain ⟨z, ⟨x, hx, rfl⟩, rfl⟩ := hy
  rw [hrad x hx t ((le_max_left 0 T).trans ht)]
  apply hepsU
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx)
    (Real.exp_pos _).le).trans_lt (by simpa only [mul_one] using hT t ((le_max_right 0 T).trans ht))

end PoincareConjecture.M25.Topology3D
