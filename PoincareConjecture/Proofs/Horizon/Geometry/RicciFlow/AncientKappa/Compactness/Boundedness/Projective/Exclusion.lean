import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Escape
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Scale

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

theorem exists_no_eventual_projective_necks
    (hc : MetricComplete (F.metric b))
    (hsec : (F.connection b).NonnegativeSectionalCurvature) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ σ : ℕ → ℕ, StrictMono σ →
      ∀ (Φ : ℕ → RoundCylinderSpace → M) (q : UnitTwoSphere),
        ¬ (∀ᶠ i in atTop,
          IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (Φ i)
            (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) ∧
          (∀ z ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹, ∀ w ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹,
            Φ i z = Φ i w ↔ w = z ∨ w = (-z.1, z.2)) ∧
          RoundCylinderClose ε 0 (fun z v w =>
            (F.connection b).scalarCurvature (S.center (σ i)) *
              roundCylinderPullback (F.metric b) (Φ i) z v w) ∧
          Φ i (q, 0) = S.center (σ i)) := by
  let := (F.metric b).toMetricSpace
  obtain ⟨ε₀, hε₀, s₀, hs₀, hbound⟩ :=
    (F.metric b).exists_remote_projective_neck_scale_lower_bound (F.connection b) hc hsec p
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall σ hσ Φ q hnecks
  have hcenters := (S.centers_exhaustion_tendsto_atTop hc hsec).comp hσ.tendsto_atTop
  have hscales := S.original_scales_tendsto_zero.comp hσ.tendsto_atTop
  have houtside := S.eventually_outside_projective_half_slabs hσ hε Φ q
    (hnecks.mono fun _ hi => ⟨hi.1.contMDiffOn, hi.2.2⟩)
  have himpossible : ∀ᶠ i : ℕ in atTop, False := by
    filter_upwards [hnecks, hcenters.eventually_ge_atTop 2,
      hscales.eventually_lt_const hs₀, houtside] with i hi hcᵢ hsᵢ hpᵢ
    have hr : 0 < 1 / Real.sqrt ((F.connection b).scalarCurvature (S.center (σ i))) :=
      one_div_pos.mpr (Real.sqrt_pos.mpr (S.scalar_pos (σ i)))
    have hnormalize :
        (1 / Real.sqrt ((F.connection b).scalarCurvature (S.center (σ i))))⁻¹ ^ 2 =
          (F.connection b).scalarCurvature (S.center (σ i)) := by
      simp only [one_div, inv_inv]
      exact Real.sq_sqrt (S.scalar_pos (σ i)).le
    have hremote : 2 ≤ busemannExhaustion p (Φ i (q, 0)) := by
      rw [hi.2.2.2]
      exact hcᵢ
    have hb := hbound ε _ hε hr hεsmall (Φ i) hi.1 hi.2.1
      (by simpa only [hnormalize] using hi.2.2.1) q hremote hpᵢ
    exact (not_lt_of_ge hb) hsᵢ
  exact (Filter.Eventually.exists himpossible).choose_spec

end PoincareConjecture.RicciFlow.SelectedAncientRescalings
