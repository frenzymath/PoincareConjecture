import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Theory
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.ExponentialTheory
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Theory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Theory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Theory
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.OrdinaryCapture

/-! Adapted from Mapher `PoincareMT/Statements/M14GeneralizedLGeometry.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

set_option autoImplicit false

open scoped Manifold ContMDiff ContDiff Bundle Topology intervalIntegral BigOperators

universe u

namespace PoincareMT

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
  /- Morgan--Tian Definition 6.26 and Proposition 6.78: attainment is
     exported on an actual stable exponential branch.  A generalized flow
     need not attain every finite action infimum. -/
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

/-! An adapted spacetime chart already includes the time coordinate. The
reduced length is compared only at actual endpoints in that chart. -/
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

/-! Corollary 6.79 uses one curvature bound on a whole past slab. The compact
neighborhood is local ODE support; short-branch confinement is a conclusion.
See `reviews/contracts/2026-09-15-m14-m15-correction-round1.md`. -/
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

/-! These records make the remaining Chapter 7/8 consumers explicit.  They
are theorem outputs, so later milestones can work from one selected density,
stable image, and scaling correspondence rather than reconstructing them. -/

end PoincareMT
