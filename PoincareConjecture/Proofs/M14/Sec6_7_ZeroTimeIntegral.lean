import PoincareConjecture.Proofs.M14.Sec6_7_SourceDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem tendsto_reducedVolume_of_eventual_stability
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0)
    {δ : ℝ} (hδ : 0 < δ)
    (H : ∀ (τ : ℝ) (_hτ : 0 < τ) (_hδ : τ < δ), M14StableSet G T τ x E)
    (hcover : ∀ Z : G.Horizontal x, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∃ hτ : 0 < τ, ∃ hτδ : τ < δ, Z ∈ (H τ hτ hτδ).carrier) :
    Tendsto (fun τ : ℝ => if hτ : 0 < τ then
      if hτδ : τ < δ then M14ReducedVolumeOnStable G T x τ (H τ hτ hτδ) else 0 else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (euclideanReducedVolume n)) := by
  classical
  let F : ℝ → G.Horizontal x → ℝ := fun τ => if hτ : 0 < τ then
    if hτδ : τ < δ then stableSourceDensity (H τ hτ hτδ) b else fun _ => 0 else fun _ => 0
  have hvalid : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ ∧ τ < δ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with τ hτ hτδ
    exact ⟨hτ, hτδ⟩
  have hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (F τ) (M14HorizontalCoordinateVolume G b) := by
    filter_upwards [hvalid] with τ hτ
    simpa only [F, dif_pos hτ.1, dif_pos hτ.2] using
      (stableSourceDensity_measurable hM04 hM12 (H τ hτ.1 hτ.2) b hb).aestronglyMeasurable
  have hbound : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ Z ∂M14HorizontalCoordinateVolume G b, ‖F τ Z‖ ≤
        Real.rpow (2 : ℝ) (n : ℝ) * Real.exp (-G.spacetime.horizontalMetric.inner x Z Z) := by
    filter_upwards [hvalid] with τ hτ
    apply Eventually.of_forall
    intro Z
    simp only [F, dif_pos hτ.1, dif_pos hτ.2, Real.norm_eq_abs,
      abs_of_nonneg (stableSourceDensity_nonneg (H τ hτ.1 hτ.2) b Z)]
    exact stableSourceDensity_le_gaussian hCoordinates hM04 hM12 (H τ hτ.1 hτ.2) b hb Z
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Real.sqrt_pos.mpr hs
  have hpoint (Z : G.Horizontal x) : Tendsto (fun τ => F τ Z) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.rpow (2 : ℝ) (n : ℝ) *
        Real.exp (-G.spacetime.horizontalMetric.inner x Z Z))) := by
    obtain ⟨τ, hτ, hτδ, hZ⟩ := (hcover Z).exists
    have hlim := (tendsto_exponentialWeightedJacobian_zero hM04 hM12 E b hb
      ((H τ hτ hτδ).survivor Z hZ) (Real.sqrt_pos.mpr hτ)).comp hsqrt
    apply hlim.congr'
    filter_upwards [hcover Z] with σ hσ
    obtain ⟨hσ, hσδ, hZσ⟩ := hσ
    simp only [Function.comp_apply, F, dif_pos hσ, dif_pos hσδ,
      stableSourceDensity, indicator_of_mem hZσ]
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun Z => Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)) hmeas hbound
      (horizontalGaussian_integrable b hb) (Eventually.of_forall hpoint)
  rw [integral_horizontalGaussian b hb] at hlim
  apply hlim.congr'
  filter_upwards [hvalid] with τ hτ
  simp only [F, dif_pos hτ.1, dif_pos hτ.2]
  exact integral_stableSourceDensity hCoordinates hM04 hM12 (H τ hτ.1 hτ.2) b hb

end PoincareConjecture.M14
