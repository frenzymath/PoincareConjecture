import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Regularity

/-! Adapted from Mapher `PoincareMT/Statements/M14GeneralizedLGeometry.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

set_option autoImplicit false

open scoped Manifold ContMDiff ContDiff Bundle Topology intervalIntegral BigOperators

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

structure M14ReducedVolumeAnalyticData
    (G : GeneralizedLGeometryTransport n X time I)
    (T τ : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E) where
  density : (G.slices (T - τ)).Point → ℝ
  density_eq : ∀ q ∈ H.endpoint_slice_map '' H.carrier, density q =
    Real.rpow τ (-(n : ℝ) / 2) *
      Real.exp (-M14ReducedLengthValue G T 0 τ x q.val)
  density_measurable_on_image :
    Measurable (fun q : H.endpoint_slice_map '' H.carrier => density q.1)
  density_nonnegative : ∀ q ∈ H.endpoint_slice_map '' H.carrier, 0 ≤ density q
  measure_data : M14MeasureJacobianData G T τ x E H
  initial_density : G.Horizontal x → ℝ
  initial_density_eq : ∀ Z, initial_density Z =
    Real.rpow (2 : ℝ) (n : ℝ) *
      Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)
  gaussian_bound : ∀ Z, Z ∈ H.carrier →
    density (H.endpoint_slice_map Z) * measure_data.jacobian Z ≤ initial_density Z
  density_integrable : MeasureTheory.IntegrableOn density
    (H.endpoint_slice_map '' H.carrier)
    (calibratedMetricVolume (G.slices (T - τ)).metricOnPoints)
  density_integrable_on_source :
    MeasureTheory.IntegrableOn
      (fun Z => density (H.endpoint_slice_map Z) * measure_data.jacobian Z)
      H.carrier measure_data.sourceMeasure
  density_change_of_variables_on_image :
    (∫ Z in H.carrier,
      density (H.endpoint_slice_map Z) * measure_data.jacobian Z
        ∂measure_data.sourceMeasure) =
      (∫ q in H.endpoint_slice_map '' H.carrier, density q
        ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints)
  backward_star : ∀ W : Set (G.Horizontal x), W ⊆ H.carrier →
    ∀ Z, Z ∈ W →
      ∃ p : M14BackwardPath G T 0 τ x (H.endpoint_map Z),
        M14IsMinimizing p ∧
        ∀ σ, σ ∈ Set.Ioc 0 τ →
          ∃ Hσ : M14StableSet G T σ x E,
            Z ∈ Hσ.carrier ∧ p.curve σ = Hσ.endpoint_map Z
  fixed_W_monotone : ∀ W : Set (G.Horizontal x), W ⊆ H.carrier →
    W.Nonempty → IsOpen W → MeasurableSet W →
    (∀ Z, Z ∈ W → ∃ p : M14BackwardPath G T 0 τ x (H.endpoint_map Z),
      M14IsMinimizing p) →
    ∀ σ, 0 < σ → σ ≤ τ →
      ∃ Hσ : M14StableSet G T σ x E,
        W ⊆ Hσ.carrier ∧
        (∫ q in H.endpoint_slice_map '' W,
          density q ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints) ≤
        (∫ q in Hσ.endpoint_slice_map '' W,
          Real.rpow σ (-(n : ℝ) / 2) *
            Real.exp (-M14ReducedLengthValue G T 0 σ x q.val)
            ∂calibratedMetricVolume (G.slices (T - σ)).metricOnPoints)

noncomputable def M14ReducedVolumeOnAnalyticCarrier
    {G : GeneralizedLGeometryTransport n X time I}
    {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
    {H : M14StableSet G T τ x E}
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    (W : Set (G.Horizontal x)) : ℝ :=
  ∫ q in H.endpoint_slice_map '' W, A.density q
    ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints

/-! Source-level Chapter 7 outputs that are not contained in one per-time
analytic witness. The selected stable family and its selected
`M14ReducedVolumeAnalyticData` are carried through every clause. This records
the regular-image consequences used in Morgan--Tian Propositions 6.78--6.81
and Theorem 8.1, pp. 142--147 and 169--171. -/
structure M14ReducedVolumeSourceCoverageData
    (G : GeneralizedLGeometryTransport n X time I) where
  zero_time_limit :
    ∀ (T : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
      (B : ℕ → Set (G.Horizontal x)) (δ : ℝ),
      0 < δ → Set.Icc (T - δ) T ⊆ I.domain →
      (∀ k, IsCompact (B k)) →
      (∀ k, B k ⊆ B (k + 1)) →
      (∀ Z, ∃ k, Z ∈ B k) →
      (K : ℕ → Set G.Point) →
      (∀ k, IsCompact (K k) ∧
        (∃ O : Set G.Point, IsOpen O ∧ x ∈ O ∧ O ⊆ K k) ∧
        (∃ R : ℝ, 0 ≤ R ∧ ∀ Z, Z ∈ B k →
          G.spacetime.horizontalMetric.inner x Z Z ≤ R)) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p : G.Point,
        G.spacetime.timeFunction p ∈ Set.Icc (T - δ) T →
          horizontalCurvatureNorm G.leafwise p ≤ C) →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ δ ∧
        ∃ H : ∀ (τ : ℝ) (_hτ : 0 < τ) (_hτ₀ : τ < τ₀),
          M14StableSet G T τ x E,
          ∃ A : ∀ (τ : ℝ) (_hτ : 0 < τ) (_hτ₀ : τ < τ₀),
            M14ReducedVolumeAnalyticData G T τ x E (H τ _hτ _hτ₀),
            (∀ (τ : ℝ) (_hτ : 0 < τ) (_hτ₀ : τ < τ₀),
              M14ReducedVolumeOnAnalyticCarrier (A τ _hτ _hτ₀)
                (H τ _hτ _hτ₀).carrier =
                M14ReducedVolumeOnStable G T x τ (H τ _hτ _hτ₀)) ∧
            (∀ k, ∃ η : ℝ, 0 < η ∧ η ≤ τ₀ ∧
              ∀ (τ : ℝ) (_hτ : 0 < τ) (_hτ₀ : τ < τ₀),
                τ < η → B k ⊆ (H τ _hτ _hτ₀).carrier ∧
                  ∀ Z, Z ∈ B k → ∀ s ∈ Set.Icc 0 τ,
                    E.gamma Z (Real.sqrt s) ∈ K k) ∧
            Filter.Tendsto
              (fun τ : ℝ =>
                if hτ : 0 < τ then
                  if hτ₀ : τ < τ₀ then
                    M14ReducedVolumeOnAnalyticCarrier (A τ hτ hτ₀)
                      (H τ hτ hτ₀).carrier
                  else 0
                else 0)
              (𝓝[>] (0 : ℝ)) (𝓝 (euclideanReducedVolume n))
  disjoint_image_additivity :
    ∀ (T τ : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
      (H : M14StableSet G T τ x E)
      (A : M14ReducedVolumeAnalyticData G T τ x E H),
      Set.InjOn H.endpoint_slice_map H.carrier ∧
      ∀ (W₁ W₂ : Set (G.Horizontal x)),
        W₁ ⊆ H.carrier → W₂ ⊆ H.carrier →
        MeasurableSet W₁ → MeasurableSet W₂ → Disjoint W₁ W₂ →
          MeasurableSet (H.endpoint_slice_map '' W₁) ∧
          MeasurableSet (H.endpoint_slice_map '' W₂) ∧
          MeasurableSet (H.endpoint_slice_map '' (W₁ ∪ W₂)) ∧
          Disjoint (H.endpoint_slice_map '' W₁)
            (H.endpoint_slice_map '' W₂) ∧
          M14ReducedVolumeOnAnalyticCarrier A (W₁ ∪ W₂) =
            M14ReducedVolumeOnAnalyticCarrier A W₁ +
              M14ReducedVolumeOnAnalyticCarrier A W₂
  terminal_W_lower_bound :
    ∀ (T τmax : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
      (τ₀ : ℝ),
      0 < τ₀ → τ₀ ≤ τmax →
      ∀ (H₀ : M14StableSet G T τ₀ x E)
        (A₀ : M14ReducedVolumeAnalyticData G T τ₀ x E H₀)
        (W : Set (G.Horizontal x)),
        IsOpen W → W.Nonempty → MeasurableSet W → W ⊆ H₀.carrier →
        ∀ l₀ V : ℝ, 0 ≤ l₀ → 0 < V →
          (∀ Z, Z ∈ W →
            M14ReducedLengthValue G T 0 τ₀ x (H₀.endpoint_map Z) ≤ l₀) →
          ENNReal.ofReal V ≤
            calibratedMetricVolume (G.slices (T - τ₀)).metricOnPoints
              (H₀.endpoint_slice_map '' W) →
          Real.rpow τ₀ (-(n : ℝ) / 2) * Real.exp (-l₀) * V ≤
              M14ReducedVolumeOnAnalyticCarrier A₀ W ∧
          ∀ τ, 0 < τ → τ ≤ τ₀ →
            ∃ Hτ : M14StableSet G T τ x E,
              W ⊆ Hτ.carrier ∧
              ∃ Aτ : M14ReducedVolumeAnalyticData G T τ x E Hτ,
                Real.rpow τ₀ (-(n : ℝ) / 2) * Real.exp (-l₀) * V ≤
                  M14ReducedVolumeOnAnalyticCarrier Aτ W

end PoincareMT
