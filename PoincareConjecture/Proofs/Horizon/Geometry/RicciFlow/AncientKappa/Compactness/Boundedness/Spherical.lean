import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Escape
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.Scale

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open Poincare.Riemannian.Soul
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow.SelectedAncientRescalings

variable {M : Type} [TopologicalSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {b κ : ℝ} {F : RicciFlow 3 M (Iic b)} {p : M}
  (S : SelectedAncientRescalings F κ p)

theorem exists_no_eventual_spherical_necks
    (hc : MetricComplete (F.metric b))
    (hsec : (F.connection b).NonnegativeSectionalCurvature) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ σ : ℕ → ℕ, StrictMono σ →
        ¬ (∀ᶠ i in atTop, ∃ N : EpsilonNeck (F.metric b),
          N.epsilon = ε ∧
          N.scale = 1 / Real.sqrt ((F.connection b).scalarCurvature (S.center (σ i))) ∧
          N.center = S.center (σ i)) := by
  let := (F.metric b).toMetricSpace
  obtain ⟨ε₀, hε₀, s₀, hs₀, hbound⟩ :=
    (F.metric b).exists_remote_neck_scale_lower_bound (F.connection b) hc hsec p
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall σ hσ hnecks
  have hcenters := (S.centers_exhaustion_tendsto_atTop hc hsec).comp hσ.tendsto_atTop
  have hscales := S.original_scales_tendsto_zero.comp hσ.tendsto_atTop
  have houtside := S.eventually_outside_spherical_half_necks hσ hε
  have himpossible : ∀ᶠ i : ℕ in atTop, False := by
    filter_upwards [hnecks, hcenters.eventually_ge_atTop 2,
      hscales.eventually_lt_const hs₀, houtside] with i hi hcᵢ hsᵢ hpᵢ
    obtain ⟨N, hNe, hNs, hNc⟩ := hi
    have hNremote : 2 ≤ busemannExhaustion p N.center := by
      rw [hNc]
      exact hcᵢ
    have hNoutside : p ∉ N.coordinate_map ''
        (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) := by
      rw [hNe]
      exact hpᵢ N hNe hNs hNc
    have hb := hbound N (hNe ▸ hεsmall) hNremote hNoutside
    rw [hNs] at hb
    exact (not_lt_of_ge hb) hsᵢ
  exact (Filter.Eventually.exists himpossible).choose_spec

end PoincareConjecture.RicciFlow.SelectedAncientRescalings
