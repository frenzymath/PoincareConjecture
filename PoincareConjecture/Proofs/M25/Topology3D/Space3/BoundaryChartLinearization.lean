import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartGermNormalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryGermIsotopy
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscShrinking












set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_boundary_chart_linearization (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ)) :
    ∃ A : (ℝ ∙ v)ᗮ ≃L[ℝ] (ℝ ∙ v)ᗮ,
      ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ y, ‖F y‖ = ‖y‖) ∧
        (∀ᶠ x in 𝓝 0, F (stereoInvFun hv (D.chart 0 + A x) : E) =
          (stereoInvFun hv (D.chart x) : E)) ∧
        ∃ C : Set E, IsCompact C ∧ C ⊆ radialStereoTarget v ∧
          ∀ y, y ∉ C → F y = y := by
  obtain ⟨A, _, h, hh, hh0, hd0, hnear⟩ := exists_normalized_chart_correction
    D.chart D.smooth D.smooth_symm
    (D.closedBall_subset_source (mem_closedBall_self zero_le_one))
  obtain ⟨Ψ, _, _, hnorm, htrack, C, hC, hCt, hfix⟩ :=
    exists_boundary_germ_isotopy_at v hv (D.chart 0) h hh hh0 hd0
  refine ⟨A, Ψ 1, hnorm 1, ?_, C, hC, hCt, hfix 1⟩
  have hAt : Tendsto A (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using A.continuous.tendsto (0 : (ℝ ∙ v)ᗮ)
  filter_upwards [hAt.eventually hnear, hAt.eventually htrack] with x hx htx
  rw [htx, ← hx, A.symm_apply_apply]



theorem exists_boundary_disc_affine_image (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ)) :
    ∃ A : (ℝ ∙ v)ᗮ ≃L[ℝ] (ℝ ∙ v)ᗮ, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ y, ‖F y‖ = ‖y‖) ∧
        (∀ x ∈ closedBall 0 1, F (stereoInvFun hv (D.chart x) : E) =
          (stereoInvFun hv (D.chart 0 + A (r • x)) : E)) ∧
        ∃ C : Set E, IsCompact C ∧ ∀ y, y ∉ C → F y = y := by
  obtain ⟨A, G, hGnorm, hGnear, C, hC, _, hGfix⟩ :=
    exists_boundary_chart_linearization v hv D
  obtain ⟨ε, hε, hεnear⟩ := Metric.mem_nhds_iff.mp hGnear
  have hsmall : ∀ᶠ t : ℝ in atTop, Real.exp (-t) < ε :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hε)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hsmall
  let t := max 0 T
  have ht : 0 ≤ t := le_max_left _ _
  have hexp : Real.exp (-t) < ε := hT t (le_max_right _ _)
  obtain ⟨Φ, _, _, hΦnorm, htrack, _, K, hK, _, hΦfix⟩ :=
    exists_boundaryDisc_shrinking_isotopy v hv D
  let F := (Φ t).trans G.symm
  refine ⟨A, Real.exp (-t), Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht),
    F, ?_, ?_, K ∪ C, hK.union hC, ?_⟩
  · intro y
    change ‖G.symm (Φ t y)‖ = ‖y‖
    rw [← hGnorm (G.symm (Φ t y)), G.apply_symm_apply, hΦnorm]
  · intro x hx
    have hxs : Real.exp (-t) • x ∈ ball 0 ε := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx)
        (Real.exp_pos _).le).trans_lt (by simpa only [mul_one] using hexp)
    change G.symm (Φ t (stereoInvFun hv (D.chart x) : E)) = _
    rw [htrack x hx t ht, ← hεnear hxs, G.symm_apply_apply]
  · intro y hy
    have hyK : y ∉ K := fun h => hy (Or.inl h)
    have hyC : y ∉ C := fun h => hy (Or.inr h)
    change G.symm (Φ t y) = y
    rw [hΦfix t y hyK]
    exact equiv_symm_fixed_of_fixed G.toEquiv (hGfix y hyC)

end PoincareConjecture.M25.Topology3D
