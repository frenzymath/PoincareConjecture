import PoincareConjecture.Proofs.M25.Topology3D.Space3.CapShrinking
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood












set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]



theorem exists_charted_cap_shrinking_isotopy (B : BallNeighborhoodChart E F)
    (u : E) (hu : ‖u‖ = 1) (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞,
      ContDiff ℝ ∞ (fun p : ℝ × F => Ψ p.1 p.2) ∧
      (∀ y, Ψ 0 y = y) ∧
      (∀ t : ℝ, 0 ≤ t → MapsTo (Ψ t) B.closedRegion B.closedRegion) ∧
      (∀ t : ℝ, 0 ≤ t → MapsTo (Ψ t)
        (B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ})
        (B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ})) ∧
      (∀ V : Set F, IsOpen V → B.chart u ∈ V → ∃ T : ℝ, 0 ≤ T ∧
        ∀ t : ℝ, T ≤ t → MapsTo (Ψ t) B.closedRegion V) ∧
      ∃ C : Set F, IsCompact C ∧ C ⊆ B.chart.target ∧ ∀ t y, y ∉ C → Ψ t y = y := by
  obtain ⟨Φ, hΦ, hzero, hball, hcap, hshrink, C, hC, hCs, hfix⟩ :=
    exists_cap_shrinking_isotopy u hu a ha B.chart.open_source B.closedBall_subset_source
  obtain ⟨Ψ, hΨ, hΨzero, htrack, hΨfix, hCimage, hCt⟩ :=
    exists_chart_transport_isotopy B.chart B.smooth B.smooth_symm Φ hΦ hzero hC hCs hfix
  refine ⟨Ψ, hΨ, hΨzero, ?_, ?_, ?_, B.chart '' C, hCimage, hCt, hΨfix⟩
  · intro t ht y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [htrack t x (B.closedBall_subset_source hx)]
    exact ⟨Φ t x, hball t ht hx, rfl⟩
  · intro t ht y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [htrack t x (B.closedBall_subset_source (mem_closedBall_zero_iff.mpr hx.1.le))]
    exact ⟨Φ t x, hcap t ht hx, rfl⟩
  · intro V hV huV
    have hus : u ∈ B.chart.source := B.closedBall_subset_source (mem_closedBall_zero_iff.mpr hu.le)
    have hn : B.chart ⁻¹' V ∈ 𝓝 u :=
      (B.chart.continuousOn.continuousAt (B.chart.open_source.mem_nhds hus)).preimage_mem_nhds
        (hV.mem_nhds huV)
    obtain ⟨eps, heps, hepsV⟩ := Metric.mem_nhds_iff.mp hn
    obtain ⟨T, hT0, hT⟩ := hshrink eps heps
    refine ⟨T, hT0, ?_⟩
    intro t ht y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [htrack t x (B.closedBall_subset_source hx)]
    exact hepsV (hT t ht hx)

end PoincareConjecture.M25.Topology3D
