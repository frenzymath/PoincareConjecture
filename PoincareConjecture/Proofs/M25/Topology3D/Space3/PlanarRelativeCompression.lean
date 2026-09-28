import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBallPair
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartedRelativeCompression











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] space3_stereographic_dimension



theorem relative_ball_compression_of_planar (hP : PlanarSchoenfliesService)
    (B : BallNeighborhoodChart E3 F)
    (c : UnitCircle → E2) (hc : IsPlanarEmbedding c) (v : UnitTwoSphere) :
    ∃ D : PlanarSchoenfliesData c,
      let Δ : Set F := B.chart ''
        ((fun x : E2 => ((stereographic' 2 v).symm (D.chart x) : E3)) '' closedBall 0 1)
      ∀ V Ω : Set F, IsOpen V → Δ ⊆ V → IsOpen Ω → B.closedRegion \ Δ ⊆ Ω →
        ∃ T : ℝ, 0 ≤ T ∧
          ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞,
            ContDiff ℝ ∞ (fun p : ℝ × F => Ψ p.1 p.2) ∧
            (∀ y, Ψ 0 y = y) ∧
            (∀ t : ℝ, 0 ≤ t → MapsTo (Ψ t) B.closedRegion B.closedRegion) ∧
            MapsTo (Ψ T) B.closedRegion V ∧
            (∀ t y, y ∈ Δ → Ψ t y = y) ∧
            ∃ C : Set F, IsCompact C ∧ C ⊆ Ω \ Δ ∧
              ∀ t y, y ∉ C → Ψ t y = y := by
  obtain ⟨D, a, ha, B', _, hclosed, _, hcap⟩ := ballPair_cap_of_planar hP B c hc v
  refine ⟨D, ?_⟩
  dsimp only
  intro V Ω hV hDV hΩ hBΩ
  have hu : ‖-(v : E3)‖ = 1 := by rw [norm_neg]; exact norm_eq_of_mem_sphere v
  have hDV' : B'.chart '' {x : E3 | ‖x‖ = 1 ∧ a ≤ ⟪-(v : E3), x⟫_ℝ} ⊆ V := by
    rwa [hcap]
  have hBΩ' : B'.closedRegion \
      (B'.chart '' {x : E3 | ‖x‖ = 1 ∧ a ≤ ⟪-(v : E3), x⟫_ℝ}) ⊆ Ω := by
    rwa [hclosed, hcap]
  have h := exists_charted_relative_cap_compression B' (-(v : E3)) hu a ha hV hDV' hΩ hBΩ'
  simpa only [hclosed, hcap] using h

end PoincareConjecture.M25.Topology3D
