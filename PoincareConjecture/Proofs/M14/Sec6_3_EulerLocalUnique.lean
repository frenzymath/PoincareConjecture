import PoincareConjecture.Proofs.M14.Sec6_3_EulerGaugeUnique
import PoincareConjecture.Proofs.M14.Sec6_3_SquareRootComparison
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import PoincareConjecture.Proofs.M08.OverlappingIntervals
import PoincareConjecture.Statements.M12GeneralizedEquation










set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}





theorem squareRootEuler_eventuallyEqWithin
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T τ₁ τ₂ σ₁ σ₂ : ℝ} {x₁ y₁ x₂ y₂ : G.Point}
    {p₁ : M14BackwardPath G T τ₁ τ₂ x₁ y₁} {p₂ : M14BackwardPath G T σ₁ σ₂ x₂ y₂}
    (R₁ : M14SquareRootPath G p₁) (R₂ : M14SquareRootPath G p₂)
    {a c s₀ : ℝ} (hac : a < c)
    (hsub₁ : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂)
    (hsub₂ : Icc a c ⊆ M14SqrtParameterInterval σ₁ σ₂)
    (E₁ : M14PullbackExtension G R₁.curve (M14SqrtParameterInterval τ₁ τ₂)
      R₁.horizontal_velocity)
    (E₂ : M14PullbackExtension G R₂.curve (M14SqrtParameterInterval σ₁ σ₂)
      R₂.horizontal_velocity)
    (heuler₁ : ∀ s ∈ Icc a c, ∀ Z : G.Horizontal (R₁.curve s),
      M14SquareRootEulerResidual G R₁ E₁ s Z = 0)
    (heuler₂ : ∀ s ∈ Icc a c, ∀ Z : G.Horizontal (R₂.curve s),
      M14SquareRootEulerResidual G R₂ E₂ s Z = 0)
    (hs₀ : s₀ ∈ Icc a c) (heq : R₁.curve s₀ = R₂.curve s₀)
    (hvel : HEq (R₁.horizontal_velocity s₀) (R₂.horizontal_velocity s₀)) :
    ∀ᶠ s in 𝓝[Icc a c] s₀,
      R₁.curve s = R₂.curve s ∧ HEq (R₁.horizontal_velocity s) (R₂.horizontal_velocity s) := by
  classical
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  obtain ⟨b, U, lift, hU, hsU, hlift, hright, hclock⟩ :=
    exists_smooth_gauge_lift G (R₁.curve s₀)
  have hR₁ := (R₁.smooth.mono R₁.interval_subset).mono hsub₁
  have hR₂ := (R₂.smooth.mono R₂.interval_subset).mono hsub₂
  have hpre₁ : R₁.curve ⁻¹' U ∈ 𝓝[Icc a c] s₀ :=
    (hR₁.continuousOn s₀ hs₀).preimage_mem_nhdsWithin (hU.mem_nhds hsU)
  have hpre₂ : R₂.curve ⁻¹' U ∈ 𝓝[Icc a c] s₀ :=
    (hR₂.continuousOn s₀ hs₀).preimage_mem_nhdsWithin (hU.mem_nhds (heq ▸ hsU))
  obtain ⟨N, hN, hsN, hNsub⟩ := mem_nhdsWithin.mp (inter_mem hpre₁ hpre₂)
  have hcore : Icc s₀ s₀ ⊆ N := by simpa only [Icc_self, singleton_subset_iff] using hsN
  obtain ⟨l, r, hal, hlr, hrc, hls, hsr, hJN, hnear⟩ :=
    M08.exists_enlarged_closed_interval hac hs₀.1 le_rfl hs₀.2 hN hcore
  have hJC : Icc l r ⊆ Icc a c := Icc_subset_Icc hal hrc
  have hmap₁ : MapsTo R₁.curve (Icc l r) U := fun s hs => (hNsub ⟨hJN hs, hJC hs⟩).1
  have hmap₂ : MapsTo R₂.curve (Icc l r) U := fun s hs => (hNsub ⟨hJN hs, hJC hs⟩).2
  let W := Classical.choice (ordinaryGaugeWitness_nonempty b hCoordinates)
  have hlocal := squareRootEuler_gauge_unique b hCoordinates hscalar W hM04
    (lift (R₁.curve s₀)).2 R₁ R₂ hlr (hJC.trans hsub₁) (hJC.trans hsub₂)
    (hlift.comp (hR₁.mono hJC) hmap₁) (hlift.comp (hR₂.mono hJC) hmap₂)
    (fun s hs => hright _ (hmap₁ hs)) (fun s hs => hright _ (hmap₂ hs))
    (fun s hs => (hclock _ (hmap₁ hs)).trans (R₁.curve_time s (hsub₁ (hJC hs))))
    (fun s hs => (hclock _ (hmap₂ hs)).trans (R₂.curve_time s (hsub₂ (hJC hs))))
    E₁ E₂ (fun s hs => heuler₁ s (hJC hs)) (fun s hs => heuler₂ s (hJC hs))
    ⟨hls, hsr⟩ heq hvel
  filter_upwards [hnear s₀ ⟨le_rfl, le_rfl⟩] with s hs
  exact ⟨hlocal hs, squareRoot_horizontalVelocity_heq_on_subset R₁ R₂
    (hJC.trans hsub₁) (hJC.trans hsub₂) hlocal hs (uniqueDiffOn_Icc hlr s hs)⟩

end PoincareConjecture.M14
