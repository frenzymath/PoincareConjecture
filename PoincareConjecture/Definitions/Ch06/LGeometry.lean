import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Definitions.Ch04.Harnack
import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Definitions.Ch01.TensorOperators
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic














set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]


noncomputable def curveVelocity (γ : ℝ → M) (τ : ℝ) : TangentSpace (𝓡 n) (γ τ) :=
  (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ τ) 1


structure SmoothAlongCurveExtensionOn (I : Set ℝ) (γ : ℝ → M)
    (Y : ∀ τ, TangentSpace (𝓡 n) (γ τ)) where
  extension : ∀ τ, τ ∈ I → Cₛ^∞⟮(𝓡 n); EuclideanSpace ℝ (Fin n),
    (TangentSpace (𝓡 n) : M → Type _)⟯
  agrees_near : ∀ τ (hτ : τ ∈ I), ∃ δ > 0, ∀ σ ∈ I, |σ - τ| < δ →
    extension τ hτ (γ σ) = Y σ


structure PointwiseSectionExtensionOn (I : Set ℝ) (γ : ℝ → M)
    (Y : ∀ τ, TangentSpace (𝓡 n) (γ τ)) where
  extension : ∀ τ, τ ∈ I → Cₛ^∞⟮(𝓡 n); EuclideanSpace ℝ (Fin n),
    (TangentSpace (𝓡 n) : M → Type _)⟯
  agrees_at : ∀ τ (hτ : τ ∈ I), extension τ hτ (γ τ) = Y τ


noncomputable def alongCovariantDerivative {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (γ : ℝ → M)
    (Y : ∀ τ, TangentSpace (𝓡 n) (γ τ))
    (I : Set ℝ) (E : SmoothAlongCurveExtensionOn I γ Y)
    (V : ∀ τ, TangentSpace (𝓡 n) (γ τ)) (τ : ℝ) (hτ : τ ∈ I) :
    TangentSpace (𝓡 n) (γ τ) :=
  (F.connection (time τ)).connection (E.extension τ hτ) (γ τ) (V τ)


noncomputable def curveVelocityWithin (γ : ℝ → M) (I : Set ℝ) (s : ℝ) :
    TangentSpace (𝓡 n) (γ s) :=
  (mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) γ I s) 1


structure ParametricAlongCurveExtensionOn (I : Set ℝ) (γ : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 n) (γ s)) where
  extension : ℝ → (x : M) → TangentSpace (𝓡 n) x
  domain : Set (ℝ × M)
  open_domain : IsOpen domain
  graph_mem : ∀ s ∈ I, (s, γ s) ∈ domain
  smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
    (fun z : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
      z.2 (extension z.1 z.2)) domain
  agrees : ∀ s ∈ I, extension s (γ s) = Y s


noncomputable def pullbackCovariantDerivative {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (γ : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 n) (γ s)) (I : Set ℝ)
    (E : ParametricAlongCurveExtensionOn I γ Y) (s : ℝ) :
    TangentSpace (𝓡 n) (γ s) :=
  deriv (fun r ↦ E.extension r (γ s)) s +
    (F.connection (time s)).connection (E.extension s) (γ s)
      (curveVelocityWithin (n := n) γ I s)


noncomputable def scalarCurvatureDifferential {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (γ : ℝ → M) (τ : ℝ) :
    TangentSpace (𝓡 n) (γ τ) →L[ℝ] ℝ :=
  mvfderiv (𝓡 n) (fun y ↦ (F.connection (time τ)).scalarCurvature y) (γ τ)


noncomputable def backwardLIntegrand {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (τ : ℝ) : ℝ :=
  Real.sqrt τ * ((F.connection (T - τ)).scalarCurvature (γ τ) +
    (F.metric (T - τ)).inner (γ τ) (curveVelocity (n := n) γ τ)
      (curveVelocity (n := n) γ τ))


noncomputable def backwardLLength {J : Set ℝ} (F : RicciFlow n M J)
    (T τ₁ τ₂ : ℝ) (γ : ℝ → M) : ℝ :=
  ∫ τ in τ₁..τ₂, backwardLIntegrand F T γ τ


structure BackwardTimePath {J : Set ℝ} (F : RicciFlow n M J)
    (T τ₁ τ₂ : ℝ) where
  curve : ℝ → M
  nonnegative : 0 ≤ τ₁
  ordered : τ₁ < τ₂
  terminal_mem : T ∈ J
  time_mem : ∀ τ ∈ Set.Icc τ₁ τ₂, T - τ ∈ J
  continuous : ContinuousOn curve (Set.Icc τ₁ τ₂)
  regular : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 curve (Set.Ioo τ₁ τ₂)
  l_integrable : IntervalIntegrable (backwardLIntegrand F T curve)
    MeasureTheory.volume τ₁ τ₂


noncomputable def backwardEulerResidual {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (I : Set ℝ)
    (E : ParametricAlongCurveExtensionOn I γ (curveVelocityWithin (n := n) γ I))
    (τ : ℝ) (W : TangentSpace (𝓡 n) (γ τ)) : ℝ :=
  (F.metric (T - τ)).inner (γ τ)
      (pullbackCovariantDerivative F (fun r ↦ T - r) γ
        (curveVelocityWithin (n := n) γ I) I E τ) W -
    (1 / 2 : ℝ) * scalarCurvatureDifferential F (fun r ↦ T - r) γ τ W +
    (1 / (2 * τ) : ℝ) * (F.metric (T - τ)).inner (γ τ)
      (curveVelocityWithin (n := n) γ I τ) W +
    2 * (F.connection (T - τ)).ricci (γ τ) (curveVelocityWithin (n := n) γ I τ) W


def backwardEulerLagrange {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (I : Set ℝ)
    (E : ParametricAlongCurveExtensionOn I γ (curveVelocityWithin (n := n) γ I)) (τ : ℝ) : Prop :=
  ∀ W : TangentSpace (𝓡 n) (γ τ), backwardEulerResidual F T γ I E τ W = 0


def IsBackwardLGeodesic {J : Set ℝ} (F : RicciFlow n M J)
    (T τ₁ τ₂ : ℝ) (p : BackwardTimePath F T τ₁ τ₂) : Prop :=
  ∃ E : ParametricAlongCurveExtensionOn (Set.Ioo τ₁ τ₂) p.curve
      (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂)),
    ∀ τ ∈ Set.Ioo τ₁ τ₂,
      backwardEulerLagrange F T p.curve (Set.Ioo τ₁ τ₂) E τ


def squareReparameterizedCurve (γ : ℝ → M) : ℝ → M := fun s ↦ γ (s ^ 2)


def sqrtParameterInterval (τ₁ τ₂ : ℝ) : Set ℝ :=
  Set.Icc (Real.sqrt τ₁) (Real.sqrt τ₂)


structure SqrtRegularPath {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) where
  curve : ℝ → M
  domain : Set ℝ
  open_domain : IsOpen domain
  interval_subset : sqrtParameterInterval τ₁ τ₂ ⊆ domain
  smooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ curve domain
  agrees : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, curve s = p.curve (s ^ 2)


noncomputable def regularizedEulerResidual {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (α : ℝ → M) (I : Set ℝ)
    (E : ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I))
    (s : ℝ) (W : TangentSpace (𝓡 n) (α s)) : ℝ :=
  (F.metric (T - s ^ 2)).inner (α s)
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
        (curveVelocityWithin (n := n) α I) I E s) W -
    2 * s ^ 2 * scalarCurvatureDifferential F (fun r ↦ T - r ^ 2) α s W +
    4 * s * (F.connection (T - s ^ 2)).ricci
      (α s) (curveVelocityWithin (n := n) α I s) W


def regularizedLGeodesicEquation {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (α : ℝ → M) (I : Set ℝ)
    (E : ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I)) (s : ℝ) : Prop :=
  ∀ W : TangentSpace (𝓡 n) (α s), regularizedEulerResidual F T α I E s W = 0


structure RegularizedLGeodesicData {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) where
  path : SqrtRegularPath p
  velocity_extension : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂)
    path.curve (curveVelocityWithin (n := n) path.curve (sqrtParameterInterval τ₁ τ₂))
  equation : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
    regularizedLGeodesicEquation F T path.curve (sqrtParameterInterval τ₁ τ₂)
      velocity_extension s


def IsMinimizingBackwardLPath {J : Set ℝ} (F : RicciFlow n M J)
    (T τ₁ τ₂ : ℝ) (p : BackwardTimePath F T τ₁ τ₂) : Prop :=
  ∀ q : BackwardTimePath F T τ₁ τ₂,
    q.curve τ₁ = p.curve τ₁ → q.curve τ₂ = p.curve τ₂ →
      backwardLLength F T τ₁ τ₂ p.curve ≤ backwardLLength F T τ₁ τ₂ q.curve


structure LVariation {J : Set ℝ} (F : RicciFlow n M J)
    (T τ₁ τ₂ : ℝ) (p : BackwardTimePath F T τ₁ τ₂) where
  family : ℝ → ℝ → M
  at_zero : ∀ τ, family τ 0 = p.curve τ
  radius : ℝ
  radius_pos : 0 < radius
  squareFamily : ℝ → ℝ → M
  squareDomain : Set (ℝ × ℝ)
  square_open : IsOpen squareDomain
  square_contains : sqrtParameterInterval τ₁ τ₂ ×ˢ Set.Ioo (-radius) radius ⊆ squareDomain
  square_smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
    (fun z : ℝ × ℝ ↦ squareFamily z.1 z.2) squareDomain
  square_agrees : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
    ∀ u ∈ Set.Ioo (-radius) radius, squareFamily s u = family (s ^ 2) u
  l_integrable : ∀ u ∈ Set.Ioo (-radius) radius,
    IntervalIntegrable (backwardLIntegrand F T (fun τ ↦ family τ u))
      MeasureTheory.volume τ₁ τ₂


def LVariation.parameterDomain {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) : Set ℝ := Set.Ioo (-V.radius) V.radius


def LVariation.baseSquareCurve {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) : ℝ → M := fun s ↦ V.squareFamily s 0


structure InitialFixedLVariation {J : Set ℝ} (F : RicciFlow n M J)
    (T τ₁ τ₂ : ℝ) (p : BackwardTimePath F T τ₁ τ₂)
    extends LVariation F T τ₁ τ₂ p where
  fixed_left : ∀ u ∈ Set.Ioo (-radius) radius, family τ₁ u = p.curve τ₁


structure FixedEndpointLVariation {J : Set ℝ} (F : RicciFlow n M J)
    (T τ₁ τ₂ : ℝ) (p : BackwardTimePath F T τ₁ τ₂)
    extends InitialFixedLVariation F T τ₁ τ₂ p where
  fixed_right : ∀ u ∈ Set.Ioo (-radius) radius, family τ₂ u = p.curve τ₂


noncomputable def variationLLength {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (u : ℝ) : ℝ :=
  backwardLLength F T τ₁ τ₂ (fun τ ↦ V.family τ u)


noncomputable def variationField {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (τ : ℝ) : TangentSpace (𝓡 n) (p.curve τ) :=
  (V.at_zero τ) ▸ curveVelocity (fun u ↦ V.family τ u) 0


noncomputable def squareVariationField {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (s : ℝ) :
    TangentSpace (𝓡 n) (V.baseSquareCurve s) :=
  curveVelocity (fun u ↦ V.squareFamily s u) 0


structure LVariationDerivativeData {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) where
  velocity_extension : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂)
    V.baseSquareCurve (curveVelocityWithin (n := n) V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂))
  variation_extension : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂)
    V.baseSquareCurve (squareVariationField V)
  endpoint_extension : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
    ParametricAlongCurveExtensionOn V.parameterDomain (V.squareFamily s)
      (curveVelocityWithin (n := n) (V.squareFamily s) V.parameterDomain)


noncomputable def firstVariationBoundaryTerm {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) : ℝ :=
  let B := fun s ↦ (F.metric (T - s ^ 2)).inner (V.baseSquareCurve s)
    (curveVelocityWithin (n := n) V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂) s)
    (squareVariationField V s)
  B (Real.sqrt τ₂) - B (Real.sqrt τ₁)


noncomputable def firstVariationResidualIntegral {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V) : ℝ :=
  ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
    -regularizedEulerResidual F T V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂)
      D.velocity_extension s (squareVariationField V s)


noncomputable def variationEndpointAcceleration {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    (s : ℝ) (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    TangentSpace (𝓡 n) (V.baseSquareCurve s) :=
  pullbackCovariantDerivative F (fun _ ↦ T - s ^ 2) (V.squareFamily s)
    (curveVelocityWithin (n := n) (V.squareFamily s) V.parameterDomain) V.parameterDomain
    (D.endpoint_extension s hs) 0


noncomputable def secondVariationBoundaryTerm {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V) : ℝ :=
  let B := fun s (hs : s ∈ sqrtParameterInterval τ₁ τ₂) ↦
    (F.metric (T - s ^ 2)).inner (V.baseSquareCurve s)
      (curveVelocityWithin (n := n) V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂) s)
      (variationEndpointAcceleration V D s hs)
  B (Real.sqrt τ₂) ⟨Real.sqrt_le_sqrt (le_of_lt p.ordered), le_rfl⟩ -
    B (Real.sqrt τ₁) ⟨le_rfl, Real.sqrt_le_sqrt (le_of_lt p.ordered)⟩


noncomputable def ricciDerivativePairing {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (U V W : TangentSpace (𝓡 n) x) : ℝ :=
  D.covariantTensorDerivative D.ricciEvaluation x ![U, V, W]


noncomputable def backwardConnectionVariationPairing {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (U V W : TangentSpace (𝓡 n) x) : ℝ :=
  ricciDerivativePairing D x U V W + ricciDerivativePairing D x V U W -
    ricciDerivativePairing D x W U V


noncomputable def secondVariationIndexDensity {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V) (s : ℝ) : ℝ :=
  let x := V.baseSquareCurve s
  let A := curveVelocityWithin (n := n) V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂) s
  let Y := squareVariationField V s
  let DY := pullbackCovariantDerivative F (fun r ↦ T - r ^ 2)
    V.baseSquareCurve (squareVariationField V) (sqrtParameterInterval τ₁ τ₂)
    D.variation_extension s
  let connection := F.connection (T - s ^ 2)
  (F.metric (T - s ^ 2)).inner x DY DY + connection.curvatureTensor x Y A A Y +
    2 * s ^ 2 * connection.hessian connection.scalarCurvature x Y Y -
    4 * s * ricciDerivativePairing connection x Y A Y +
    2 * s * ricciDerivativePairing connection x A Y Y


noncomputable def secondVariationIndexForm {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V) : ℝ :=
  ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, secondVariationIndexDensity V D s


structure SqrtRegularField {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (R : SqrtRegularPath p) (Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)) where
  field : ∀ s, TangentSpace (𝓡 n) (R.curve s)
  agrees : ∀ s (hs : s ∈ sqrtParameterInterval τ₁ τ₂),
    field s = (R.agrees s hs).symm ▸ Y (s ^ 2)
  extension : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) R.curve field
  derivative_extension : ParametricAlongCurveExtensionOn (sqrtParameterInterval τ₁ τ₂) R.curve
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) R.curve field
      (sqrtParameterInterval τ₁ τ₂) extension)


noncomputable def SqrtRegularField.firstDerivative {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    {R : SqrtRegularPath p} {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)}
    (Q : SqrtRegularField R Y) (s : ℝ) : TangentSpace (𝓡 n) (R.curve s) :=
  pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) R.curve Q.field
    (sqrtParameterInterval τ₁ τ₂) Q.extension s


noncomputable def SqrtRegularField.secondDerivative {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    {R : SqrtRegularPath p} {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)}
    (Q : SqrtRegularField R Y) (s : ℝ) : TangentSpace (𝓡 n) (R.curve s) :=
  pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) R.curve Q.firstDerivative
    (sqrtParameterInterval τ₁ τ₂) Q.derivative_extension s


noncomputable def regularizedJacobiResidual {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (R : RegularizedLGeodesicData p) {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)}
    (Q : SqrtRegularField R.path Y) (s : ℝ)
    (W : TangentSpace (𝓡 n) (R.path.curve s)) : ℝ :=
  let x := R.path.curve s
  let A := curveVelocityWithin (n := n) R.path.curve (sqrtParameterInterval τ₁ τ₂) s
  let connection := F.connection (T - s ^ 2)
  (F.metric (T - s ^ 2)).inner x (Q.secondDerivative s) W +
    connection.curvatureTensor x (Q.field s) A W A -
    2 * s * backwardConnectionVariationPairing connection x A (Q.field s) W -
    2 * s ^ 2 * connection.hessian connection.scalarCurvature x (Q.field s) W +
    4 * s * ricciDerivativePairing connection x (Q.field s) A W +
    4 * s * connection.ricci x (Q.firstDerivative s) W


def IsLJacobiField {J : Set ℝ} (F : RicciFlow n M J)
    (T τ₁ τ₂ : ℝ) (p : BackwardTimePath F T τ₁ τ₂)
    (Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)) : Prop :=
  ∃ R : RegularizedLGeodesicData p, ∃ Q : SqrtRegularField R.path Y,
    Y τ₁ = 0 ∧ ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      ∀ W : TangentSpace (𝓡 n) (R.path.curve s), regularizedJacobiResidual R Q s W = 0


def HasLJacobiInitialDerivative {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (R : RegularizedLGeodesicData p) (Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ))
    (Z : TangentSpace (𝓡 n) (p.curve τ₁)) : Prop :=
  ∃ Q : SqrtRegularField R.path Y,
    let hbase : R.path.curve (Real.sqrt τ₁) = p.curve τ₁ :=
      (R.path.agrees (Real.sqrt τ₁)
        ⟨le_rfl, Real.sqrt_le_sqrt (le_of_lt p.ordered)⟩).trans
          (congrArg p.curve (Real.sq_sqrt p.nonnegative))
    Q.firstDerivative (Real.sqrt τ₁) = hbase.symm ▸ Z


def CompleteBoundedCurvatureOn {J : Set ℝ} (F : RicciFlow n M J)
    (I : Set ℝ) [T3Space M] : Prop :=
  (∀ t ∈ I, MetricComplete (F.metric t)) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ I, ∀ x : M,
      |(F.connection t).curvatureTensorNorm x| ≤ K


noncomputable def reducedLength {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p q : M) (τ : ℝ) : ℝ :=
  if _hτ : 0 < τ then
    sInf {L : ℝ |
      ∃ path : BackwardTimePath F T 0 τ,
        path.curve 0 = p ∧ path.curve τ = q ∧
          L = backwardLLength F T 0 τ path.curve} / (2 * Real.sqrt τ)
  else 0

end PoincareConjecture
