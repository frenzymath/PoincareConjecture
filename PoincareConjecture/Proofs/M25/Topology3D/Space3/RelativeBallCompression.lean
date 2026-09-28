import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartedRelativeCompression

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_nested_ball_compression (A B : BallNeighborhoodChart E F)
    (u : E) (hu : ‖u‖ = 1) (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (hnest : B.closedRegion ⊆ A.closedRegion)
    (hcontact : B.closedRegion ∩ A.boundary ⊆
      B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ})
    {V : Set F} (hV : IsOpen V)
    (hcapV : B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} ⊆ V) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞,
        ContDiff ℝ ∞ (fun p : ℝ × F => Ψ p.1 p.2) ∧
        (∀ y, Ψ 0 y = y) ∧
        (∀ t : ℝ, Ψ t '' A.closedRegion = A.closedRegion) ∧
        (∀ t : ℝ, 0 ≤ t → MapsTo (Ψ t) B.closedRegion B.closedRegion) ∧
        MapsTo (Ψ T) B.closedRegion V ∧
        (∀ t y, y ∈ B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} → Ψ t y = y) ∧
        ∃ C : Set F, IsCompact C ∧ C ⊆ A.inside ∧ ∀ t y, y ∉ C → Ψ t y = y := by
  have hΩ : B.closedRegion \ (B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}) ⊆
      A.inside := by
    intro y hy
    have hyA := hnest hy.1
    rw [← A.inside_union_boundary] at hyA
    rcases hyA with hin | hbd
    · exact hin
    · exact (hy.2 (hcontact ⟨hy.1, hbd⟩)).elim
  obtain ⟨T, hT, Ψ, hΨ, hzero, hball, hfinal, hcap, C, hC, hCs, hfix⟩ :=
    exists_charted_relative_cap_compression B u hu a ha hV hcapV A.inside_open hΩ
  have hAC : A.inside ⊆ A.closedRegion := image_mono ball_subset_closedBall
  have hAfixed (t : ℝ) (y : F) (hy : y ∉ A.closedRegion) : Ψ t y = y :=
    hfix t y (fun hc => hy (hAC (hCs hc).1))
  refine ⟨T, hT, Ψ, hΨ, hzero, ?_, hball, hfinal, hcap,
    C, hC, fun _ hc => (hCs hc).1, hfix⟩
  intro t
  apply Subset.antisymm
  · exact (equiv_mapsTo_of_fixed_compl (Ψ t).toEquiv (hAfixed t)).image_subset
  · intro y hy
    refine ⟨(Ψ t).symm y, ?_, (Ψ t).apply_symm_apply y⟩
    apply equiv_mapsTo_of_fixed_compl (Ψ t).symm.toEquiv ?_ hy
    intro z hz
    exact equiv_symm_fixed_of_fixed (Ψ t).toEquiv (hAfixed t z hz)

theorem exists_disjoint_ball_compression (A B : BallNeighborhoodChart E F)
    (u : E) (hu : ‖u‖ = 1) (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (hcontact : B.closedRegion ∩ A.closedRegion ⊆
      B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ})
    {V : Set F} (hV : IsOpen V)
    (hcapV : B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} ⊆ V) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞,
        ContDiff ℝ ∞ (fun p : ℝ × F => Ψ p.1 p.2) ∧
        (∀ y, Ψ 0 y = y) ∧
        (∀ t y, y ∈ A.closedRegion → Ψ t y = y) ∧
        (∀ t : ℝ, 0 ≤ t → MapsTo (Ψ t) B.closedRegion B.closedRegion) ∧
        MapsTo (Ψ T) B.closedRegion V ∧
        (∀ t y, y ∈ B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} → Ψ t y = y) ∧
        ∃ C : Set F, IsCompact C ∧ C ⊆ A.closedRegionᶜ ∧
          ∀ t y, y ∉ C → Ψ t y = y := by
  have hΩ : B.closedRegion \ (B.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}) ⊆
      A.closedRegionᶜ := by
    intro y hy hyA
    exact hy.2 (hcontact ⟨hy.1, hyA⟩)
  obtain ⟨T, hT, Ψ, hΨ, hzero, hball, hfinal, hcap, C, hC, hCs, hfix⟩ :=
    exists_charted_relative_cap_compression B u hu a ha hV hcapV
      A.closedRegion_compact.isClosed.isOpen_compl hΩ
  refine ⟨T, hT, Ψ, hΨ, hzero, ?_, hball, hfinal, hcap,
    C, hC, fun _ hc => (hCs hc).1, hfix⟩
  intro t y hy
  exact hfix t y (fun hc => (hCs hc).1 hy)

end PoincareConjecture.M25.Topology3D
