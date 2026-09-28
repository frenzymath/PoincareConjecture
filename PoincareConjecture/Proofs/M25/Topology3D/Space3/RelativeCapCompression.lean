import PoincareConjecture.Proofs.M25.Topology3D.Space3.RelativeFlowLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CapPreservation











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_relative_cap_compression (u : E) (hu : ‖u‖ = 1)
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    {V Ω : Set E} (hV : IsOpen V)
    (hcapV : {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} ⊆ V)
    (hΩ : IsOpen Ω)
    (hBΩ : closedBall 0 1 \ {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} ⊆ Ω) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        ContDiff ℝ ∞ (fun p : ℝ × E => Ψ p.1 p.2) ∧
        (∀ x, Ψ 0 x = x) ∧
        (∀ t : ℝ, 0 ≤ t → MapsTo (Ψ t) (closedBall 0 1) (closedBall 0 1)) ∧
        MapsTo (Ψ T) (closedBall 0 1) V ∧
        (∀ t x, ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ → Ψ t x = x) ∧
        ∃ C : Set E, IsCompact C ∧
          C ⊆ Ω \ {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} ∧
          ∀ t x, x ∉ C → Ψ t x = x := by
  obtain ⟨χ, hχ, hrange, hzero, hone⟩ := exists_capContraction_cutoff a ha.1
  obtain ⟨f, hf, hfc, _, hnear⟩ := exists_compactField_extension
    (isCompact_closedBall (0 : E) 1) isOpen_univ (subset_univ _)
    (capContractionField χ u) (capContractionField_contDiff χ hχ u).contDiffOn
  have hag : EqOn f (capContractionField χ u) (closedBall 0 1) := by
    intro x hx
    exact (eventually_nhdsSet_iff_forall.mp hnear x hx).self_of_nhds
  obtain ⟨k, l, hk, hl⟩ := compactField_bounds f hf hfc
  have hinward (x : E) (hx : ‖x‖ = 1) : ⟪x, f x⟫_ℝ ≤ 0 := by
    rw [hag (mem_closedBall_zero_iff.mpr hx.le)]
    exact capContractionField_inward χ hrange hzero u hu x hx
  have hD : IsClosed {x : E | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} :=
    (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_le continuous_const (innerSL ℝ u).continuous)
  have huV : u ∈ V := hcapV ⟨hu, by
    rw [real_inner_self_eq_norm_sq, hu, one_pow]
    exact ha.2.le⟩
  obtain ⟨eps, heps, hepsV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds huV)
  obtain ⟨T, hT, hshrink⟩ :=
    capFlow_eventually_mapsTo_ball χ hrange hzero u hu f hk hl hag eps heps
  refine ⟨T, hT, ?_⟩
  exact exists_relative_ball_compression f hf hfc hk hl hinward hD hV hcapV hΩ hBΩ hT
    (fun t ht => capFlow_mapsTo_cap χ hrange hzero u hu f hk hl hag a
      (by linarith [ha.1]) hone t ht.1)
    (fun _ hx => hepsV (hshrink T le_rfl hx))

end PoincareConjecture.M25.Topology3D
