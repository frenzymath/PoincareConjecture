import PoincareConjecture.Proofs.M25.Topology3D.Space3.RelativeCapCompression
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem exists_charted_relative_cap_compression (B : BallNeighborhoodChart E F)
    (u : E) (hu : ‖u‖ = 1) (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    {V Ω : Set F} (hV : IsOpen V)
    (hcapV : B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} ⊆ V)
    (hΩ : IsOpen Ω)
    (hBΩ : B.closedRegion \ (B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}) ⊆ Ω) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞,
        ContDiff ℝ ∞ (fun p : ℝ × F => Ψ p.1 p.2) ∧
        (∀ y, Ψ 0 y = y) ∧
        (∀ t : ℝ, 0 ≤ t → MapsTo (Ψ t) B.closedRegion B.closedRegion) ∧
        MapsTo (Ψ T) B.closedRegion V ∧
        (∀ t y, y ∈ B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} → Ψ t y = y) ∧
        ∃ C : Set F, IsCompact C ∧
          C ⊆ Ω \ (B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}) ∧
          ∀ t y, y ∉ C → Ψ t y = y := by
  let D : Set E := {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}
  have hDs : D ⊆ B.chart.source := by
    intro x hx
    exact B.closedBall_subset_source (mem_closedBall_zero_iff.mpr hx.1.le)
  have hDV : D ⊆ B.chart.source ∩ B.chart ⁻¹' V := by
    intro x hx
    exact ⟨hDs hx, hcapV ⟨x, hx, rfl⟩⟩
  have hsupport : closedBall (0 : E) 1 \ D ⊆ B.chart.source ∩ B.chart ⁻¹' Ω := by
    intro x hx
    refine ⟨B.closedBall_subset_source hx.1, hBΩ ⟨⟨x, hx.1, rfl⟩, ?_⟩⟩
    rintro ⟨z, hz, heq⟩
    have hzx := B.chart.injOn (hDs hz) (B.closedBall_subset_source hx.1) heq
    exact hx.2 (hzx ▸ hz)
  obtain ⟨T, hT, Φ, hΦ, hzero, hball, hfinal, hcap, C, hC, hCs, hfix⟩ :=
    exists_relative_cap_compression u hu a ha
      (B.chart.isOpen_inter_preimage hV) hDV
      (B.chart.isOpen_inter_preimage hΩ) hsupport
  have hCsource : C ⊆ B.chart.source := fun _ hx => (hCs hx).1.1
  obtain ⟨Ψ, hΨ, hΨzero, htrack, hΨfix, hCimage, _⟩ :=
    exists_chart_transport_isotopy B.chart B.smooth B.smooth_symm Φ hΦ hzero hC hCsource hfix
  refine ⟨T, hT, Ψ, hΨ, hΨzero, ?_, ?_, ?_, B.chart '' C, hCimage, ?_, hΨfix⟩
  · intro t ht y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [htrack t x (B.closedBall_subset_source hx)]
    exact ⟨Φ t x, hball t ht hx, rfl⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [htrack T x (B.closedBall_subset_source hx)]
    exact (hfinal hx).2
  · intro t y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [htrack t x (hDs hx), hcap t x hx]
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨(hCs hx).1.2, ?_⟩
    rintro ⟨z, hz, heq⟩
    have hzx := B.chart.injOn (hDs hz) (hCsource hx) heq
    exact (hCs hx).2 (hzx ▸ hz)

end PoincareConjecture.M25.Topology3D
