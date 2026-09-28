import PoincareConjecture.Proofs.M25.Topology3D.Space3.SharedBoundaryTangency
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartedBallInvariance
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldFlowTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_sharedBoundary_preserving_isotopy (A B : BallNeighborhoodChart E F)
    (V : E → E) (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVs : tsupport V ⊆ A.chart.source)
    (hBt : A.chart '' tsupport V ⊆ B.chart.target)
    (hpatch : ∀ x ∈ tsupport V, A.chart x ∈ B.boundary →
      ‖x‖ = 1 ∧ ⟪x, V x⟫_ℝ = 0 ∧
        ∀ᶠ z in 𝓝 x, ‖z‖ = 1 → A.chart z ∈ B.boundary)
    {k l : ℝ≥0} (hk : LipschitzWith k V) (hl : ∀ x, ‖V x‖ ≤ l) :
    ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞,
      ContDiff ℝ ∞ (fun p : ℝ × F => Ψ p.1 p.2) ∧
      (∀ y, Ψ 0 y = y) ∧
      (∀ t : ℝ, Ψ t '' B.closedRegion = B.closedRegion) ∧
      (∀ t x, x ∈ A.chart.source →
        Ψ t (A.chart x) = A.chart (boundedFlow V hk hl x t)) ∧
      ∀ t y, y ∉ A.chart '' tsupport V → Ψ t y = y := by
  obtain ⟨W, hW, hWc, hWs, hpush⟩ :=
    exists_chart_field_extension A.chart A.smooth A.smooth_symm V hV hVc hVs
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds W hW hWc
  have htan (q : E) (hq : ‖q‖ = 1) :
      ⟪q, fderiv ℝ B.chart.symm (B.chart q) (W (B.chart q))⟫_ℝ = 0 := by
    by_cases hqW : B.chart q ∈ tsupport W
    · obtain ⟨x, hx, heq⟩ := hWs hqW
      have hqB : B.chart q ∈ B.boundary :=
        ⟨q, mem_sphere_zero_iff_norm.mpr hq, rfl⟩
      obtain ⟨hxnorm, hxtan, hxpatch⟩ := hpatch x hx (heq.symm ▸ hqB)
      have hcoord : B.chart.symm (A.chart x) = q := by
        rw [heq, B.chart.left_inv (B.closedBall_subset_source
          (mem_closedBall_zero_iff.mpr hq.le))]
      have ht := chartTransition_tangent A B x (V x) hxnorm
        (hBt ⟨x, hx, rfl⟩) hxpatch hxtan
      rw [← heq, hpush x (hVs hx), ← hcoord]
      exact ht
    · rw [image_eq_zero_of_notMem_tsupport hqW, map_zero, inner_zero_right]
  let Ψ := fun t => boundedFlowDiffeomorph W hK hL hW hWc t
  refine ⟨Ψ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (boundedFlow_contDiff W hK hL hW hWc).comp
      (contDiff_snd.prodMk contDiff_fst)
  · intro y
    exact boundedFlow_zero W hK hL y
  · intro t
    exact boundedFlow_image_charted_ball B W hW hWc (hWs.trans hBt) hK hL htan t
  · intro t x hx
    exact boundedFlow_chart_pushforward A.chart A.smooth V W hk hl hK hL hVs hpush hx t
  · intro t y hy
    exact boundedFlow_eq_self W hK hL y
      (image_eq_zero_of_notMem_tsupport (fun h => hy (hWs h))) t

end PoincareConjecture.M25.Topology3D
