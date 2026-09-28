import PoincareConjecture.Statements.M14PathCalculus
import PoincareConjecture.Statements.M14Exponential
import PoincareConjecture.Definitions.M14MeasureTransport
import PoincareConjecture.Statements.M12GeneralizedEquation
import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Statements.Ch06.LGeometry
import PoincareConjecture.Statements.Ch06.ReducedLength
import PoincareConjecture.Statements.Ch06.ReducedVolume

set_option autoImplicit false

open scoped Manifold ContMDiff ContDiff Bundle Topology intervalIntegral BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

def M14FiniteValueStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point),
    M14FiniteValueDomain G T τ₁ τ₂ x y →
      ∃ L : ℝ, L = M14ActionValue G T τ₁ τ₂ x y ∧
        ∃ a ∈ M14ActionSet G T τ₁ τ₂ x y, L ≤ a

def M14AttainmentStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=

  ∀ (T τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E)
    (Z : G.Horizontal x), Z ∈ H.carrier →
      ∃ p : M14BackwardPath G T 0 τ x (H.endpoint_map Z),
        Set.EqOn p.curve (fun r => E.gamma Z (Real.sqrt r)) (Set.Icc 0 τ) ∧
        M14IsMinimizing p ∧
        M14BackwardLAction G p = M14ActionValue G T 0 τ x (H.endpoint_map Z)

noncomputable def M14ReducedLengthGradientNormSq
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ : ℝ} (x q : G.Point)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal q)) : ℝ :=
  ∑ i, (mvfderiv (spacetimeModel n)
    (M14ReducedLengthAt G T τ₁ x) q
      (b i).val) ^ 2

noncomputable def M14ReducedLengthLaplacian
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ : ℝ} (x : G.Point)
    (q : (G.slices (T - τ)).Point) : ℝ :=
  (G.leafwise.sliceConnection (T - τ)).laplacian
    (fun r => M14ReducedLengthValue G T τ₁ τ x r.val) q

noncomputable def M14ReducedLengthHessianPairing
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ : ℝ} (q : (G.slices (T - τ)).Point)
    (l : G.Point → ℝ)
    (v w : G.Horizontal q.val) : ℝ :=
  let j := (G.slices (T - τ)).tangentEquiv q
  LeviCivitaData.hessian (G.leafwise.sliceConnection (T - τ))
    (fun r => l r.val) q (j.symm v) (j.symm w)

structure M14RegularFormulaData
    (G : GeneralizedLGeometryTransport n X time I)
    (T τ : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E) (Z : G.Horizontal x)
    (p : M14BackwardPath G T 0 τ x (H.endpoint_map Z)) where
  tau_pos : 0 < τ
  carrier_mem : Z ∈ H.carrier
  path_minimizing : M14IsMinimizing p
  path_endpoint : p.curve τ = H.endpoint_map Z
  gradient_basis : Module.Basis (Fin n) ℝ (G.Horizontal (H.endpoint_map Z))
  gradient_basis_orthonormal : ∀ i j,
    G.spacetime.horizontalMetric.inner (H.endpoint_map Z)
      (gradient_basis i) (gradient_basis j) = if i = j then 1 else 0
  regular_neighborhood : Set G.Point
  regular_neighborhood_open : IsOpen regular_neighborhood
  regular_center_mem : H.endpoint_map Z ∈ regular_neighborhood
  regular_representative : G.Point → ℝ
  regular_representative_eq : ∀ w ∈ regular_neighborhood,
    regular_representative w = M14ReducedLengthAt G T 0 x w
  regular_spacetime_smooth :
    ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      regular_representative regular_neighborhood
  regular_space_smooth :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun q : (G.slices (T - τ)).Point => regular_representative q.val)
      (H.endpoint_slice_map Z)
  scalar_time_derivative : ℝ → ℝ
  scalar_time_derivative_spec : ∀ s ∈ Set.Ioo 0 τ,
    scalar_time_derivative s = M14BackwardTimeDerivative G
      (horizontalScalarCurvature G.leafwise) (p.curve s)
  kplain_integrable : IntervalIntegrable
    (fun s => s * Real.sqrt s *
      M14GeneralizedHarnackDensity G p scalar_time_derivative s)
    MeasureTheory.volume 0 τ
  reduced_length_time_derivative :
    M14BackwardTimeDerivative G regular_representative (H.endpoint_map Z) =
      M14BackwardTimeDerivative G (M14ReducedLengthAt G T 0 x) (H.endpoint_map Z)
  delta : ℝ
  delta_spec : delta =
    (n : ℝ) / (2 * τ) -
      horizontalScalarCurvature G.leafwise (H.endpoint_map Z) -
      M14GeneralizedKIntegral G p scalar_time_derivative /
        (2 * τ * Real.sqrt τ) -
      M14ReducedLengthLaplacian (τ₁ := 0) G x (H.endpoint_slice_map Z)
  delta_nonnegative : 0 ≤ delta
  partial_tau_identity :
    M14BackwardTimeDerivative G (M14ReducedLengthAt G T 0 x) (H.endpoint_map Z) =
      horizontalScalarCurvature G.leafwise (H.endpoint_map Z) -
        M14ReducedLengthValue G T 0 τ x (H.endpoint_map Z) / τ +
        M14GeneralizedKIntegral G p scalar_time_derivative /
          (2 * τ * Real.sqrt τ)
  gradient_identity :
    M14ReducedLengthGradientNormSq (T := T) (τ₁ := 0) G x (H.endpoint_map Z)
      gradient_basis =
      M14ReducedLengthValue G T 0 τ x (H.endpoint_map Z) / τ -
        M14GeneralizedKIntegral G p scalar_time_derivative /
          (τ * Real.sqrt τ) -
        horizontalScalarCurvature G.leafwise (H.endpoint_map Z)
  laplacian_bound :
    M14ReducedLengthLaplacian (τ₁ := 0) G x (H.endpoint_slice_map Z) ≤
      (n : ℝ) / (2 * τ) -
        horizontalScalarCurvature G.leafwise (H.endpoint_map Z) -
        M14GeneralizedKIntegral G p scalar_time_derivative /
          (2 * τ * Real.sqrt τ)
  first_delta_identity :
    M14BackwardTimeDerivative G regular_representative (H.endpoint_map Z) +
        M14ReducedLengthLaplacian (τ₁ := 0) G x (H.endpoint_slice_map Z) -
        ((n : ℝ) / 2 - M14ReducedLengthValue G T 0 τ x
          (H.endpoint_map Z)) / τ = -delta
  second_delta_identity :
    M14BackwardTimeDerivative G regular_representative (H.endpoint_map Z) -
        M14ReducedLengthLaplacian (τ₁ := 0) G x (H.endpoint_slice_map Z) +
        M14ReducedLengthGradientNormSq (T := T) (τ₁ := 0) G x
        (H.endpoint_map Z) gradient_basis +
        - horizontalScalarCurvature G.leafwise (H.endpoint_map Z) +
        (n : ℝ) / (2 * τ) = delta
  third_delta_identity :
    2 * M14ReducedLengthLaplacian (τ₁ := 0) G x (H.endpoint_slice_map Z) -
        M14ReducedLengthGradientNormSq (T := T) (τ₁ := 0) G x
          (H.endpoint_map Z) gradient_basis +
        horizontalScalarCurvature G.leafwise (H.endpoint_map Z) +
        (M14ReducedLengthValue G T 0 τ x (H.endpoint_map Z) - (n : ℝ)) / τ =
      -2 * delta
  sharp_hessian_identity :
    M14ReducedLengthLaplacian (τ₁ := 0) G x (H.endpoint_slice_map Z) =
      (n : ℝ) / (2 * τ) -
        horizontalScalarCurvature G.leafwise (H.endpoint_map Z) -
        M14GeneralizedKIntegral G p scalar_time_derivative /
          (2 * τ * Real.sqrt τ) →
    ∀ v w : G.Horizontal (H.endpoint_map Z),
      horizontalRicci G.leafwise (H.endpoint_map Z) v w +
        M14ReducedLengthHessianPairing G (H.endpoint_slice_map Z)
          regular_representative
          ((H.endpoint_slice_map_val Z carrier_mem).symm ▸ v)
          ((H.endpoint_slice_map_val Z carrier_mem).symm ▸ w) =
          G.spacetime.horizontalMetric.inner (H.endpoint_map Z) v w / (2 * τ)

def M14RegularFormulaStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
    (z : G.Horizontal x × ℝ), z ∈ M14JointDomain G E →
    ∃ τ : ℝ, ∃ H : M14StableSet G T τ x E,
      0 < τ ∧ z.1 ∈ H.carrier ∧ z.2 = Real.sqrt τ ∧
      ∃ p : M14BackwardPath G T 0 τ x (H.endpoint_map z.1),
        M14IsMinimizing p ∧ Nonempty (M14RegularFormulaData G T τ x E H z.1 p)

def M14PositiveStartCorrectionStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y), 0 < τ₁ →
    M14IsMinimizing p →
    ∀ U : Set G.Point, IsOpen U → y ∈ U →
    U ⊆ {q | τ₁ < T - G.spacetime.timeFunction q} →
    ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (M14ReducedLengthAt G T τ₁ x) U →
    MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n)
      p.curve (Set.Icc τ₁ τ₂) τ₁ →
    mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) p.curve
      (Set.Icc τ₁ τ₂) τ₁ (1 : ℝ) =
        -G.spacetime.timeVector (p.curve τ₁) + (p.horizontal_velocity τ₁).val →
    let scalar_time_derivative := fun s => M14BackwardTimeDerivative G
      (horizontalScalarCurvature G.leafwise) (p.curve s)
    ∃ Cinitial Kplain Kshift : ℝ,
      Kplain = M14GeneralizedKIntegral G p scalar_time_derivative ∧
      Cinitial = Real.rpow (τ₁ / τ₂) (3 / 2 : ℝ) *
        (horizontalScalarCurvature G.leafwise (p.curve τ₁) +
          G.spacetime.horizontalMetric.inner (p.curve τ₁)
            (p.horizontal_velocity τ₁) (p.horizontal_velocity τ₁)) ∧
      Kshift = ∫ s in τ₁..τ₂,
        Real.sqrt s * (Real.sqrt s - Real.sqrt τ₁) ^ 2 *
          M14GeneralizedHarnackDensity G p scalar_time_derivative s ∧
      ∃ extension : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂)
          p.horizontal_velocity,
        M14EulerEquation G p extension ∧
      ∃ basis : Module.Basis (Fin n) ℝ (G.Horizontal y),
        (∀ i j, G.spacetime.horizontalMetric.inner y (basis i) (basis j) =
          if i = j then 1 else 0) ∧
        M14BackwardTimeDerivative G (M14ReducedLengthAt G T τ₁ x) y =
          horizontalScalarCurvature G.leafwise y -
            M14ReducedLengthValue G T τ₁ τ₂ x y / τ₂ +
            Kplain / (2 * τ₂ * Real.sqrt τ₂) - Cinitial / 2 ∧
        M14ReducedLengthGradientNormSq (T := T) (τ₁ := τ₁) G x y basis =
          M14ReducedLengthValue G T τ₁ τ₂ x y / τ₂ -
            Kplain / (τ₂ * Real.sqrt τ₂) -
            horizontalScalarCurvature G.leafwise y + Cinitial ∧
        ∃ q : (G.slices (T - τ₂)).Point, q.val = y ∧
          M14ReducedLengthLaplacian (τ₁ := τ₁) G x q ≤
            (n : ℝ) /
                (2 * Real.sqrt τ₂ * (Real.sqrt τ₂ - Real.sqrt τ₁)) -
              horizontalScalarCurvature G.leafwise y -
              Kshift / (2 * Real.sqrt τ₂ * (Real.sqrt τ₂ - Real.sqrt τ₁) ^ 2)

noncomputable def M14ReducedVolumeOnStable
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : G.Point) (τ : ℝ)
    {E : M14ExponentialFamily G T x} (H : M14StableSet G T τ x E) : ℝ :=
  ∫ q in H.endpoint_slice_map '' H.carrier,
    Real.rpow τ (-(n : ℝ) / 2) *
      Real.exp (-M14ReducedLengthValue G T 0 τ x q.val)
    ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints

def M14MeasureTransportStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    Nonempty (M14MeasureJacobianData G T τ x E H)

def M14ReducedVolumeStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
    (τmax : ℝ), 0 < τmax →
    ∀ Hmax : M14StableSet G T τmax x E,
      ∀ τ, 0 < τ → τ ≤ τmax →
      ∃ Hτ : M14StableSet G T τ x E,
        Hmax.carrier ⊆ Hτ.carrier ∧
          M14ReducedVolumeOnStable G T x τmax Hmax ≤
          M14ReducedVolumeOnStable G T x τ Hτ

def M14ChartProductLipschitzOn
    (G : GeneralizedLGeometryTransport n X time I)
    (f : G.Point → ℝ) (z₀ : G.Point)
    (U : Set G.Point) : Prop :=
  IsOpen U ∧ z₀ ∈ U ∧
    U ⊆ (extChartAt (spacetimeModel n) z₀).source ∧
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ U, ∀ b ∈ U,
        |f a - f b| ≤ C *
          ‖(extChartAt (spacetimeModel n) z₀) a -
            (extChartAt (spacetimeModel n) z₀) b‖

def M14LocalLipschitzStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E) (Z : G.Horizontal x), Z ∈ H.carrier →
    ∀ N F₀ : Set G.Point,
      IsOpen N → H.endpoint_map Z ∈ N →
      N ⊆ {q | 0 < T - G.spacetime.timeFunction q} →
      N ⊆ F₀ →
      (∀ q ∈ N, ∃ p : M14BackwardPath G T 0
          (T - G.spacetime.timeFunction q) x q,
        M14IsMinimizing p ∧
        ∀ s ∈ Set.Icc 0 (T - G.spacetime.timeFunction q), p.curve s ∈ F₀) →
      (∃ C_R : ℝ, 0 ≤ C_R ∧
        ∀ q ∈ F₀, ∀ v u : G.Horizontal q,
          |horizontalRicci G.leafwise q v u| ≤ C_R *
            Real.sqrt (G.spacetime.horizontalMetric.inner q v v) *
            Real.sqrt (G.spacetime.horizontalMetric.inner q u u)) →
      (∃ C_grad : ℝ, 0 ≤ C_grad ∧
        ∀ q ∈ F₀, ∀ v : G.Horizontal q,
          |M14HorizontalScalarDifferential G q v.val| ≤ C_grad *
            Real.sqrt (G.spacetime.horizontalMetric.inner q v v)) →
      ∃ U : Set G.Point, IsOpen U ∧
        H.endpoint_map Z ∈ U ∧ U ⊆ N ∧
        M14ChartProductLipschitzOn G
          (M14ReducedLengthAt G T 0 x) (H.endpoint_map Z) U

def M14SmallTimeCoverageStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
    (B : Set (G.Horizontal x)) (K : Set G.Point)
    (δ : ℝ), 0 < δ → Set.Icc (T - δ) T ⊆ I.domain → IsCompact B →
    IsCompact K →
    (∃ O : Set G.Point, IsOpen O ∧ x ∈ O ∧ O ⊆ K) →
    (∃ R : ℝ, 0 ≤ R ∧ ∀ Z, Z ∈ B →
      G.spacetime.horizontalMetric.inner x Z Z ≤ R) →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ p : G.Point,
      G.spacetime.timeFunction p ∈ Set.Icc (T - δ) T →
        horizontalCurvatureNorm G.leafwise p ≤ C) →
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ δ ∧
      ∀ τ, 0 < τ → τ < τ₀ →
        ∃ H : M14StableSet G T τ x E, B ⊆ H.carrier ∧
          ∀ Z, Z ∈ B → ∀ s ∈ Set.Icc 0 τ,
            E.gamma Z (Real.sqrt s) ∈ K

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

structure M14AnalyticRescalingData
    (G : GeneralizedLGeometryTransport n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (G' : GeneralizedLGeometryTransport n X
      (fun x => parabolicTime Q a (time x)) (parabolicInterval Q hQ a I)) where
  chartedSpace_eq : G'.spacetime.chartedSpace = G.spacetime.chartedSpace
  point_equiv : Diffeomorph (spacetimeModel n) (spacetimeModel n) G.Point G'.Point ∞
  point_equiv_eq : ∀ p, point_equiv p = p
  point_differential : ∀ p (Z : TangentSpace (spacetimeModel n) p),
    (show SpacetimeModelVector n from
      mfderiv (spacetimeModel n) (spacetimeModel n) point_equiv p Z) = Z
  point_time : ∀ p,
    G'.spacetime.timeFunction (point_equiv p) =
      parabolicTime Q a (G.spacetime.timeFunction p)
  timeVector_map : ∀ p,
    mfderiv (spacetimeModel n) (spacetimeModel n) point_equiv p
      (G.spacetime.timeVector p) = Q • G'.spacetime.timeVector (point_equiv p)
  horizontal_map : ∀ p, G.Horizontal p ≃L[ℝ] G'.Horizontal (point_equiv p)
  horizontal_differential : ∀ p (v : G.Horizontal p),
    (horizontal_map p v).val =
      mfderiv (spacetimeModel n) (spacetimeModel n) point_equiv p v.val
  horizontal_metric : ∀ p v w,
    G'.spacetime.horizontalMetric.inner (point_equiv p)
      (horizontal_map p v) (horizontal_map p w) =
      Q * G.spacetime.horizontalMetric.inner p v w
  scalar_curvature : ∀ p,
    horizontalScalarCurvature G'.leafwise (point_equiv p) =
      Q⁻¹ * horizontalScalarCurvature G.leafwise p
  slice_identification : ∀ t,
    Diffeomorph (𝓡 n) (𝓡 n) (G.slices t).Point
      (G'.slices (parabolicTime Q a t)).Point ∞
  slice_identification_eq : ∀ t x,
    (slice_identification t x).val = point_equiv x.val
  slice_tangent : ∀ t (x : (G.slices t).Point) (v : TangentSpace (𝓡 n) x),
    (show SpacetimeModelVector n from
      ((G'.slices (parabolicTime Q a t)).tangentEquiv (slice_identification t x)
        (mfderiv (𝓡 n) (𝓡 n) (slice_identification t) x v)).val) =
      (horizontal_map x.val ((G.slices t).tangentEquiv x v)).val
  slice_metric : ∀ t,
    MetricHomothety (G.slices t).metricOnPoints
      (G'.slices (parabolicTime Q a t)).metricOnPoints (slice_identification t) Q
  initial_equiv : ∀ x : G.Point,
    G.Horizontal x ≃L[ℝ] G'.Horizontal (point_equiv x)
  initial_equiv_eq : ∀ x v,
    initial_equiv x v = (Real.sqrt Q)⁻¹ • horizontal_map x v
  initial_equiv_isometry : ∀ x v w,
    G'.spacetime.horizontalMetric.inner (point_equiv x)
      (initial_equiv x v) (initial_equiv x w) =
      G.spacetime.horizontalMetric.inner x v w
  path_map : ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point),
    M14BackwardPath G T τ₁ τ₂ x y →
    M14BackwardPath G' (parabolicTime Q a T) (Q * τ₁) (Q * τ₂)
      (point_equiv x) (point_equiv y)
  path_map_eq : ∀ T τ₁ τ₂ x y p s,
    (path_map T τ₁ τ₂ x y p).curve (Q * s) = point_equiv (p.curve s)
  action_scale : ∀ T τ₁ τ₂ x y p,
    M14BackwardLAction G' (path_map T τ₁ τ₂ x y p) =
      Real.sqrt Q * M14BackwardLAction G p
  path_inverse : ∀ T τ₁ τ₂ x y
    (p' : M14BackwardPath G' (parabolicTime Q a T) (Q * τ₁) (Q * τ₂)
      (point_equiv x) (point_equiv y)),
    ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
      ∀ s, p'.curve (Q * s) = point_equiv (p.curve s)
  path_inverse_exact : ∀ T τ₁ τ₂ x y
    (p' : M14BackwardPath G' (parabolicTime Q a T) (Q * τ₁) (Q * τ₂)
      (point_equiv x) (point_equiv y)),
    ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
      path_map T τ₁ τ₂ x y p = p'
  path_minimizer_iff : ∀ T τ₁ τ₂ x y
    (p : M14BackwardPath G T τ₁ τ₂ x y),
    M14IsMinimizing (path_map T τ₁ τ₂ x y p) ↔ M14IsMinimizing p
  path_inverse_action : ∀ T τ₁ τ₂ x y
    (p' : M14BackwardPath G' (parabolicTime Q a T) (Q * τ₁) (Q * τ₂)
      (point_equiv x) (point_equiv y)),
    ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
      path_map T τ₁ τ₂ x y p = p' ∧
      M14BackwardLAction G' p' =
        Real.sqrt Q * M14BackwardLAction G p
  reduced_length_scale : ∀ T τ₁ τ₂ x y,
    0 < τ₂ → M14FiniteValueDomain G T τ₁ τ₂ x y →
    M14ReducedLengthValue G' (parabolicTime Q a T) (Q * τ₁) (Q * τ₂)
        (point_equiv x) (point_equiv y) =
      M14ReducedLengthValue G T τ₁ τ₂ x y
  density : ∀ (_T _τ : ℝ) (_x _q : G.Point), ℝ
  density_eq : ∀ T τ x q,
    0 < τ → G.spacetime.timeFunction x = T →
    G.spacetime.timeFunction q = T - τ → M14FiniteValueDomain G T 0 τ x q →
    density T τ x q = Real.rpow τ (-(n : ℝ) / 2) *
      Real.exp (-M14ReducedLengthValue G T 0 τ x q)
  density' : ∀ (_T _τ : ℝ) (_x _q : G'.Point), ℝ
  density'_eq : ∀ T τ x q,
    0 < τ → G'.spacetime.timeFunction x = T →
    G'.spacetime.timeFunction q = T - τ → M14FiniteValueDomain G' T 0 τ x q →
    density' T τ x q = Real.rpow τ (-(n : ℝ) / 2) *
      Real.exp (-M14ReducedLengthValue G' T 0 τ x q)
  density_scale : ∀ T τ x q,
    0 < τ → G.spacetime.timeFunction x = T →
    G.spacetime.timeFunction q = T - τ → M14FiniteValueDomain G T 0 τ x q →
    density' (parabolicTime Q a T) (Q * τ) (point_equiv x) (point_equiv q) =
      Real.rpow Q (-(n : ℝ) / 2) * density T τ x q
  target_family : ∀ (T : ℝ) (x : G.Point) (_E : M14ExponentialFamily G T x),
    M14ExponentialFamily G' (parabolicTime Q a T) (point_equiv x)
  exponential_domain_transport : ∀ T x (E : M14ExponentialFamily G T x) Z s,
    (Z, s) ∈ E.domain ↔
      (initial_equiv x Z, Real.sqrt Q * s) ∈ (target_family T x E).domain
  exponential_transport : ∀ T x (E : M14ExponentialFamily G T x) Z s,
    (Z, s) ∈ E.domain →
      (target_family T x E).gamma (initial_equiv x Z) (Real.sqrt Q * s) =
        point_equiv (E.gamma Z s)
  stable_transport : ∀ (T τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
      ∃ H' : M14StableSet G' (parabolicTime Q a T) (Q * τ)
          (point_equiv x) (target_family T x E),
        (∀ Z, Z ∈ H.carrier ↔ initial_equiv x Z ∈ H'.carrier) ∧
        ∃ D : M14MeasureJacobianData G T τ x E H,
          ∃ D' : M14MeasureJacobianData G' (parabolicTime Q a T) (Q * τ)
              (point_equiv x) (target_family T x E) H',
            (∀ Z, Z ∈ H.carrier →
              D'.jacobian (initial_equiv x Z) =
                Real.rpow Q ((n : ℝ) / 2) * D.jacobian Z) ∧
            (fun q => point_equiv q.val) ''
                (H.endpoint_slice_map '' H.carrier) =
              (fun q => q.val) '' (H'.endpoint_slice_map '' H'.carrier) ∧
            (∫ q in H.endpoint_slice_map '' H.carrier,
                density T τ x q.val ∂calibratedMetricVolume
                  (G.slices (T - τ)).metricOnPoints) =
              ∫ q' in H'.endpoint_slice_map '' H'.carrier,
                density' (parabolicTime Q a T) (Q * τ) (point_equiv x) q'.val
                  ∂calibratedMetricVolume
                    (G'.slices (parabolicTime Q a T - Q * τ)).metricOnPoints
  joint_domain_transport : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) Z s,
    (Z, s) ∈ M14JointDomain G E ↔
      (initial_equiv x Z, Real.sqrt Q * s) ∈
        M14JointDomain G' (target_family T x E)
  jacobian_data : ∀ (T τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    Nonempty (M14MeasureJacobianData G T τ x E H)

def M14AnalyticRescalingConclusion
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (Q : ℝ) (hQ : 0 < Q) (a : ℝ),
    ∃ G' : GeneralizedLGeometryTransport n X
      (fun x => parabolicTime Q a (time x)) (parabolicInterval Q hQ a I),
      Nonempty (M14AnalyticRescalingData G Q hQ a G')

structure M14OrdinaryProviders (n : ℕ) : Prop where
  m08 : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M]
    [SecondCountableTopology M]
    (J : Set ℝ) (F : RicciFlow n M J) (T τmax : ℝ),
    T ∈ J → 0 < τmax → Set.Icc (T - τmax) T ⊆ J →
    CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T) →
    Nonempty (LGeodesicTheory F T τmax)
  m09 : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M]
    [SecondCountableTopology M]
    (J : Set ℝ) (F : RicciFlow n M J) (T τmax : ℝ),
    T ∈ J → 0 < τmax → Set.Icc (T - τmax) T ⊆ J →
    CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T) →
    LGeodesicTheory F T τmax → Nonempty (ReducedLengthDifferentialTheory F T τmax)
  m10 : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (J : Set ℝ) (F : RicciFlow n M J) (T τmax : ℝ),
    T ∈ J → 0 < τmax → Set.Icc (T - τmax) T ⊆ J →
    CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T) →
    LGeodesicTheory F T τmax → ReducedLengthDifferentialTheory F T τmax →
    Nonempty (ReducedVolumeTheory F T τmax)

structure M14OrdinaryCaptureData
    (G : GeneralizedLGeometryTransport n X time I)
    (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    [T3Space C]
    [ConnectedSpace C] [SecondCountableTopology C]
    [MeasurableSpace C] [BorelSpace C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder G.spacetime
      (G.timeIntervals.interval K) C)
    (g : SpacetimeCylinderMetric e)
    (F : RicciFlow n C K.domain) (T τmax : ℝ) where
  metric_eq : Set.EqOn F.metric g.metric K.domain
  point_map : G.Point → C
  point_map_on_cylinder : ∀ (s : (G.timeIntervals.interval K).Point) (c : C),
    point_map (e.toSpacetime (s, c)) = c
  point_map_continuous : ContinuousOn point_map (Set.range e.toSpacetime)
  path_map : ∀ (τ₁ τ₂ : ℝ) (x y : G.Point),
    ∀ p : M14BackwardPath G T τ₁ τ₂ x y,
      (∀ s ∈ Set.Icc τ₁ τ₂, p.curve s ∈ Set.range e.toSpacetime) →
      BackwardTimePath F T τ₁ τ₂
  path_start_eq : ∀ τ₁ τ₂ x y (p : M14BackwardPath G T τ₁ τ₂ x y) hcaptured,
    (path_map τ₁ τ₂ x y p hcaptured).curve τ₁ = point_map x
  path_end_eq : ∀ τ₁ τ₂ x y (p : M14BackwardPath G T τ₁ τ₂ x y) hcaptured,
    (path_map τ₁ τ₂ x y p hcaptured).curve τ₂ = point_map y
  path_curve_eq : ∀ τ₁ τ₂ x y (p : M14BackwardPath G T τ₁ τ₂ x y) hcaptured,
    ∀ s ∈ Set.Icc τ₁ τ₂,
      point_map (p.curve s) = (path_map τ₁ τ₂ x y p hcaptured).curve s
  path_capture_eq : ∀ τ₁ τ₂ x y (p : M14BackwardPath G T τ₁ τ₂ x y) hcaptured,
    ∀ (s : ℝ) (hs : s ∈ Set.Icc τ₁ τ₂),
      e.toSpacetime
        ((⟨T - s, (path_map τ₁ τ₂ x y p hcaptured).time_mem s hs⟩,
          (path_map τ₁ τ₂ x y p hcaptured).curve s)) = p.curve s
  path_lift : ∀ (τ₁ τ₂ : ℝ) (q : BackwardTimePath F T τ₁ τ₂),
    ∃ p : M14BackwardPath G T τ₁ τ₂
      (e.toSpacetime
        ((⟨T - τ₁, q.time_mem τ₁
          ⟨le_rfl, le_of_lt q.ordered⟩⟩, q.curve τ₁)))
      (e.toSpacetime
        ((⟨T - τ₂, q.time_mem τ₂
          ⟨le_of_lt q.ordered, le_rfl⟩⟩, q.curve τ₂))),
      ∀ (s : ℝ) (hs : s ∈ Set.Icc τ₁ τ₂),
        e.toSpacetime ((⟨T - s, q.time_mem s hs⟩, q.curve s)) = p.curve s
  capture_from_start : ∀ (τ₁ τ₂ : ℝ) (x y : G.Point),
    τ₂ ≤ τmax → x ∈ Set.range e.toSpacetime →
    ∀ p : M14BackwardPath G T τ₁ τ₂ x y,
      ∀ s ∈ Set.Icc τ₁ τ₂, p.curve s ∈ Set.range e.toSpacetime

structure M14OrdinaryCaptureOutput
    (G : GeneralizedLGeometryTransport n X time I)
    (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    [T3Space C]
    [ConnectedSpace C] [SecondCountableTopology C]
    [MeasurableSpace C] [BorelSpace C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder G.spacetime
      (G.timeIntervals.interval K) C)
    (g : SpacetimeCylinderMetric e)
    (F : RicciFlow n C K.domain) (T τmax : ℝ)
    (D : M14OrdinaryCaptureData G C K e g F T τmax) where
  L : LGeodesicTheory F T τmax
  Dlength : ReducedLengthDifferentialTheory F T τmax
  V : ReducedVolumeTheory F T τmax
  action_transport : ∀ (τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hcaptured : ∀ s ∈ Set.Icc τ₁ τ₂, p.curve s ∈ Set.range e.toSpacetime),
      backwardLLength F T τ₁ τ₂
      (D.path_map τ₁ τ₂ x y p hcaptured).curve = M14BackwardLAction G p
  captured_action_value_eq : ∀ (τ₁ τ₂ : ℝ) (x y : G.Point),
    0 ≤ τ₁ → τ₁ < τ₂ → τ₂ ≤ τmax →
    x ∈ Set.range e.toSpacetime → y ∈ Set.range e.toSpacetime →
    M14ActionValue G T τ₁ τ₂ x y =
      sInf {a | ∃ p : M14BackwardPath G T τ₁ τ₂ x y,
        (∀ s ∈ Set.Icc τ₁ τ₂, p.curve s ∈ Set.range e.toSpacetime) ∧
        M14BackwardLAction G p = a}
  reduced_length_transport : ∀ (τ : ℝ) (x y : G.Point),
    0 < τ → τ ≤ τmax →
    G.spacetime.timeFunction x = T →
    G.spacetime.timeFunction y = T - τ →
    x ∈ Set.range e.toSpacetime → y ∈ Set.range e.toSpacetime →
    M14ReducedLengthValue G T 0 τ x y =
      reducedLength F T (D.point_map x) (D.point_map y) τ
  minimizing_transport : ∀ (τ₁ τ₂ : ℝ) (x y : G.Point), τ₂ ≤ τmax →
    x ∈ Set.range e.toSpacetime →
    ∀ (p : M14BackwardPath G T τ₁ τ₂ x y)
      (hcaptured : ∀ s ∈ Set.Icc τ₁ τ₂, p.curve s ∈ Set.range e.toSpacetime),
      M14IsMinimizing p ↔
        IsMinimizingBackwardLPath F T τ₁ τ₂ (D.path_map τ₁ τ₂ x y p hcaptured)
  regular_locus_transport : ∀ (τ : ℝ) (x : G.Point), 0 < τ → τ < τmax →
    x ∈ Set.range e.toSpacetime →
    ∀ (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E)
      (Z : G.Horizontal x), Z ∈ H.carrier →
    (Z, Real.sqrt τ) ∈ M14JointDomain G E →
    ∀ p : M14BackwardPath G T 0 τ x (H.endpoint_map Z), M14IsMinimizing p →
    (∀ s ∈ Set.Icc 0 τ, p.curve s = E.gamma Z (Real.sqrt s)) →
    ∀ hcaptured : ∀ s ∈ Set.Icc 0 τ, p.curve s ∈ Set.range e.toSpacetime,
      ∃ r : ReducedLengthRegularPoint F T τmax
          (D.point_map x) (D.point_map (H.endpoint_map Z)) τ,
        r.path.curve = (D.path_map 0 τ x (H.endpoint_map Z) p hcaptured).curve
  volume_transport : ∀ (τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    τ ≤ τmax → x ∈ Set.range e.toSpacetime →
    M14ReducedVolumeOnStable G T x τ H =
      reducedVolumeOn F T (D.point_map x) τ
        (D.point_map '' ((fun q => q.val) ''
          (H.endpoint_slice_map '' H.carrier)))
  endpoint_image_captured : ∀ (τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    τ ≤ τmax → x ∈ Set.range e.toSpacetime →
    (fun q => q.val) '' (H.endpoint_slice_map '' H.carrier) ⊆
      Set.range e.toSpacetime
  slice_measure_transport : ∀ (τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    τ ≤ τmax → x ∈ Set.range e.toSpacetime →
    calibratedMetricVolume (G.slices (T - τ)).metricOnPoints
      (H.endpoint_slice_map '' H.carrier) =
      calibratedMetricVolume (F.metric (T - τ))
        (D.point_map '' ((fun q => q.val) ''
          (H.endpoint_slice_map '' H.carrier)))

  captured_stable_image_full_measure : ∀ (τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E),
    τ < τmax → x ∈ Set.range e.toSpacetime →
    calibratedMetricVolume (G.slices (T - τ)).metricOnPoints
      ({q | q.val ∈ Set.range e.toSpacetime} \
        (H.endpoint_slice_map '' H.carrier)) = 0

  captured_slice_measure_transport : ∀ (τ : ℝ), 0 < τ → τ < τmax →
    ∀ A : Set (G.slices (T - τ)).Point, MeasurableSet A →
    (fun q => q.val) '' A ⊆ Set.range e.toSpacetime →
      calibratedMetricVolume (G.slices (T - τ)).metricOnPoints A =
        calibratedMetricVolume (F.metric (T - τ))
          (D.point_map '' ((fun q => q.val) '' A))

def M14OrdinaryCaptureStatement
    (G : GeneralizedLGeometryTransport n X time I)
    (O : M14OrdinaryProviders.{u} n) : Prop :=
  ∀ (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] [ConnectedSpace C] [T3Space C]
    [SecondCountableTopology C] [MeasurableSpace C] [BorelSpace C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder G.spacetime
      (G.timeIntervals.interval K) C)
    (g : SpacetimeCylinderMetric e)
    (F : RicciFlow n C K.domain)
    (T τmax : ℝ) (hT : T ∈ K.domain) (hτ : 0 < τmax)
    (hK : Set.Icc (T - τmax) T ⊆ K.domain)
    (hcurv : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T)),
    ∀ capture : M14OrdinaryCaptureData G C K e g F T τmax,
      ∃ out : M14OrdinaryCaptureOutput G C K e g F T τmax capture,
        out.L = Classical.choice (O.m08 C K.domain F T τmax hT hτ hK hcurv) ∧
        out.Dlength = Classical.choice (O.m09 C K.domain F T τmax hT hτ hK hcurv out.L) ∧
        out.V = Classical.choice (O.m10 C K.domain F T τmax hT hτ hK hcurv out.L out.Dlength)

structure GeneralizedLGeometryConclusion
    (G : GeneralizedLGeometryTransport n X time I) : Prop where
  path_calculus : M14PathCalculusConclusion G
  exponential : M14ExponentialConclusion G
  finite_value : M14FiniteValueStatement G
  attainment : M14AttainmentStatement G
  regular_formulas : M14RegularFormulaStatement G
  positive_start_correction : M14PositiveStartCorrectionStatement G
  measure_transport : M14MeasureTransportStatement G
  reduced_volume : M14ReducedVolumeStatement G
  local_lipschitz : M14LocalLipschitzStatement G
  small_time_coverage : M14SmallTimeCoverageStatement G
  reduced_volume_analytic : ∀ (T τ : ℝ) (x : G.Point),
    ∀ (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E),
      Nonempty (M14ReducedVolumeAnalyticData G T τ x E H)
  reduced_volume_source : Nonempty (M14ReducedVolumeSourceCoverageData G)
  analytic_rescaling : M14AnalyticRescalingConclusion G
  ordinary_capture : ∀ O : M14OrdinaryProviders.{u} n, M14OrdinaryCaptureStatement G O

structure GeneralizedLGeometryTheory (n : ℕ) : Prop where
  conclusion : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
    (I : SpacetimeInterval) (G : GeneralizedLGeometryTransport n X time I),
    Nonempty (GeneralizedLGeometryConclusion G)

end PoincareConjecture
