import PoincareConjecture.Definitions.M14GeneralizedLGeometry
import PoincareConjecture.Definitions.Ch01.TensorOperators
import PoincareConjecture.Definitions.Ch01.ScalarOperators
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}
variable {G : GeneralizedLGeometryTransport n X time I}

def M14SqrtParameterInterval (τ₁ τ₂ : ℝ) : Set ℝ :=
  Set.Icc (Real.sqrt τ₁) (Real.sqrt τ₂)

structure M14PullbackExtension
    (G : GeneralizedLGeometryTransport n X time I)
    (γ : ℝ → G.Point) (J : Set ℝ)
    (Y : ∀ s, G.Horizontal (γ s)) where
  extension : ℝ → HorizontalSection G.spacetime
  domain : Set G.Point
  domain_open : IsOpen domain
  graph_mem : ∀ s ∈ J, γ s ∈ domain
  spatial_smooth : ∀ r, IsSmoothHorizontalSectionOn G.spacetime (extension r) domain
  joint_smooth : ∃ U : Set (ℝ × G.Point), IsOpen U ∧
    (∀ s ∈ J, (s, γ s) ∈ U) ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.spacetime.Horizontal) z.2 (extension z.1 z.2)) U
  agrees : ∀ s ∈ J, extension s (γ s) = Y s
  parameter_derivative : ∀ s ∈ J, ∃ d : G.Horizontal (γ s),
    HasDerivAt (fun r : ℝ => extension r (γ s)) d s

noncomputable def M14HorizontalCovariantDerivative
    (G : GeneralizedLGeometryTransport n X time I)
    (γ : ℝ → G.Point) (J : Set ℝ)
    (Y : ∀ s, G.Horizontal (γ s))
    (E : M14PullbackExtension G γ J Y) (s : ℝ) : G.Horizontal (γ s) :=
  deriv (fun r : ℝ => E.extension r (γ s)) s +
    rawHorizontalCovariantDerivative G.leafwise (E.extension s) (γ s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))

noncomputable def M14HorizontalScalarDifferential
    (G : GeneralizedLGeometryTransport n X time I)
    (p : G.Point) : TangentSpace (spacetimeModel n) p →L[ℝ] ℝ :=
  mvfderiv (spacetimeModel n) (fun q : G.Point =>
    horizontalScalarCurvature G.leafwise q) p

noncomputable def M14EulerResidual
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (E : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂) p.horizontal_velocity)
    (τ : ℝ) (W : G.Horizontal (p.curve τ)) : ℝ :=
  G.spacetime.horizontalMetric.inner (p.curve τ)
      (M14HorizontalCovariantDerivative G p.curve (Set.Ioo τ₁ τ₂)
        p.horizontal_velocity E τ) W -
    (1 / 2 : ℝ) * M14HorizontalScalarDifferential G (p.curve τ) W.val +
    (1 / (2 * τ) : ℝ) * G.spacetime.horizontalMetric.inner (p.curve τ)
      (p.horizontal_velocity τ) W +
    2 * horizontalRicci G.leafwise (p.curve τ) (p.horizontal_velocity τ) W

def M14EulerEquation
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (E : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂) p.horizontal_velocity) : Prop :=
  ∀ τ ∈ Set.Ioo τ₁ τ₂, ∀ W : G.Horizontal (p.curve τ), M14EulerResidual G p E τ W = 0

structure M14SquareRootPath
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y) where
  curve : ℝ → G.Point
  domain : Set ℝ
  interval_subset : M14SqrtParameterInterval τ₁ τ₂ ⊆ domain
  smooth : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ curve domain
  agrees : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, curve s = p.curve (s ^ 2)
  curve_time : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
    G.spacetime.timeFunction (curve s) = T - s ^ 2
  horizontal_velocity : ∀ s, G.Horizontal (curve s)
  horizontal_agrees : ∀ s (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)),
    horizontal_velocity s =
      (agrees s ⟨le_of_lt hs.1, le_of_lt hs.2⟩).symm ▸
        ((2 * s) • p.horizontal_velocity (s ^ 2))
  derivative_eq : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
    mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) curve
      (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ) =
      -(2 * s) • G.spacetime.timeVector (curve s) + (horizontal_velocity s).val

noncomputable def M14SquareRootVelocity
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    (R : M14SquareRootPath G p) (s : ℝ) : G.Horizontal (R.curve s) :=
  R.horizontal_velocity s

noncomputable def M14SquareRootEulerResidual
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity)
    (s : ℝ) (W : G.Horizontal (R.curve s)) : ℝ :=
  G.spacetime.horizontalMetric.inner (R.curve s)
      (M14HorizontalCovariantDerivative G R.curve
        (M14SqrtParameterInterval τ₁ τ₂) R.horizontal_velocity E s) W -
    2 * s ^ 2 * M14HorizontalScalarDifferential G (R.curve s) W.val +
    4 * s * horizontalRicci G.leafwise (R.curve s)
      (M14SquareRootVelocity R s) W

noncomputable def M14HorizontalRicciDerivativePairing
    (G : GeneralizedLGeometryTransport n X time I)
    (p : G.Point) (U V W : G.Horizontal p) : ℝ :=
  let t := G.spacetime.timeFunction p
  let x := spacetimeSlicePoint G.slices p
  let j := (G.slices t).tangentEquiv x
  (G.leafwise.sliceConnection t).covariantTensorDerivative
    (G.leafwise.sliceConnection t).ricciEvaluation x ![
      j.symm U, j.symm V, j.symm W]

noncomputable def M14BcalPairing
    (G : GeneralizedLGeometryTransport n X time I)
    (p : G.Point) (U V W : G.Horizontal p) : ℝ :=
  M14HorizontalRicciDerivativePairing G p U V W +
    M14HorizontalRicciDerivativePairing G p V U W -
    M14HorizontalRicciDerivativePairing G p W U V

noncomputable def M14HorizontalHessianPairing
    (G : GeneralizedLGeometryTransport n X time I)
    (p : G.Point) (U V : G.Horizontal p) : ℝ :=
  let t := G.spacetime.timeFunction p
  let x := spacetimeSlicePoint G.slices p
  let j := (G.slices t).tangentEquiv x
  LeviCivitaData.hessian (G.leafwise.sliceConnection t)
    (G.leafwise.sliceConnection t).scalarCurvature x (j.symm U) (j.symm V)

structure M14JacobiFieldData
    (G : GeneralizedLGeometryTransport n X time I)
    (γ : ℝ → G.Point) (J : Set ℝ) where
  field : ∀ s, G.Horizontal (γ s)
  extension : M14PullbackExtension G γ J field
  derivative_extension : M14PullbackExtension G γ J
    (fun s => M14HorizontalCovariantDerivative G γ J field extension s)

noncomputable def M14JacobiFirstDerivative
    {γ : ℝ → G.Point} {J : Set ℝ}
    (Q : M14JacobiFieldData G γ J) (s : ℝ) : G.Horizontal (γ s) :=
  M14HorizontalCovariantDerivative G γ J Q.field Q.extension s

noncomputable def M14JacobiSecondDerivative
    {γ : ℝ → G.Point} {J : Set ℝ}
    (Q : M14JacobiFieldData G γ J) (s : ℝ) : G.Horizontal (γ s) :=
  M14HorizontalCovariantDerivative G γ J
    (fun r => M14JacobiFirstDerivative Q r) Q.derivative_extension s

noncomputable def M14JacobiResidual
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    (R : M14SquareRootPath G p)
    (Q : M14JacobiFieldData G R.curve (M14SqrtParameterInterval τ₁ τ₂))
    (s : ℝ) (W : G.Horizontal (R.curve s)) : ℝ :=
  let q := R.curve s
  let A := M14SquareRootVelocity R s
  let Y := Q.field s
  let DY := M14JacobiFirstDerivative Q s
  G.spacetime.horizontalMetric.inner q (M14JacobiSecondDerivative Q s) W +
    horizontalRiemann G.leafwise q Y A W A -
    2 * s * M14BcalPairing G q A Y W -
    2 * s ^ 2 * M14HorizontalHessianPairing G q Y W +
    4 * s * M14HorizontalRicciDerivativePairing G q Y A W +
    4 * s * horizontalRicci G.leafwise q DY W

structure M14LVariationData
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (R : M14SquareRootPath G p) where
  family : ℝ → ℝ → G.Point
  family_velocity : ∀ u τ, G.Horizontal (family τ u)
  family_at_zero : ∀ τ, family τ 0 = p.curve τ
  radius : ℝ
  radius_pos : 0 < radius
  parameterDomain : Set ℝ := Set.Ioo (-radius) radius
  parameterDomain_eq : parameterDomain = Set.Ioo (-radius) radius
  parameterDomain_nonempty : parameterDomain.Nonempty
  family_time : ∀ u ∈ parameterDomain, ∀ τ ∈ Set.Icc τ₁ τ₂,
    G.spacetime.timeFunction (family τ u) = T - τ
  family_derivative : ∀ u ∈ parameterDomain, ∀ τ ∈ Set.Ioo τ₁ τ₂,
    mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => family r u) τ (1 : ℝ) =
      -G.spacetime.timeVector (family τ u) + (family_velocity u τ).val
  squareFamily : ℝ → ℝ → G.Point
  squareDomain : Set (ℝ × ℝ)
  square_contains : M14SqrtParameterInterval τ₁ τ₂ ×ˢ parameterDomain ⊆ squareDomain
  square_smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
    (spacetimeModel n) ∞ (fun z => squareFamily z.1 z.2) squareDomain
  square_agrees : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
    ∀ u ∈ parameterDomain, squareFamily s u = family (s ^ 2) u
  square_base : ∀ s, squareFamily s 0 = R.curve s
  square_horizontal_velocity : ∀ s u, G.Horizontal (squareFamily s u)
  square_horizontal_agrees : ∀ s (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
      u (hu : u ∈ parameterDomain),
    square_horizontal_velocity s u =
      (square_agrees s hs u hu).symm ▸ ((2 * s) • family_velocity u (s ^ 2))

  left_endpoint_fixed : Prop
  left_endpoint_fixed_spec : left_endpoint_fixed ↔
    (∀ u ∈ parameterDomain, family τ₁ u = p.curve τ₁)
  right_endpoint_fixed : Prop
  right_endpoint_fixed_spec : right_endpoint_fixed ↔
    (∀ u ∈ parameterDomain, family τ₂ u = p.curve τ₂)
  action_integrable : ∀ u ∈ parameterDomain,
    IntervalIntegrable
      (M14RawLIntegrand G (fun τ => family τ u) (family_velocity u))
      MeasureTheory.volume τ₁ τ₂

noncomputable def M14VariationAction
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R)) (u : ℝ) : ℝ :=
  ∫ τ in τ₁..τ₂,
    M14RawLIntegrand G (fun r => V.family r u) (V.family_velocity u) τ

noncomputable def M14VariationField
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R)) (s : ℝ) :
    G.Horizontal (R.curve s) :=
  (V.square_base s).symm ▸
    G.spacetime.horizontalProjection (V.squareFamily s 0)
      (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n)
        (fun u => V.squareFamily s u) 0 (1 : ℝ))

noncomputable def M14EndpointVariationField
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R)) (s u : ℝ) :
    G.Horizontal (V.squareFamily s u) :=
  G.spacetime.horizontalProjection (V.squareFamily s u)
    (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n)
      (fun r => V.squareFamily s r) u (1 : ℝ))

structure M14VariationDerivativeData
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R)) where
  base_extension : M14PullbackExtension G R.curve
    (M14SqrtParameterInterval τ₁ τ₂) R.horizontal_velocity
  variation_extension : M14PullbackExtension G R.curve
    (M14SqrtParameterInterval τ₁ τ₂) (M14VariationField V)
  endpoint_extension : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
    M14PullbackExtension G (fun u => V.squareFamily s u) V.parameterDomain
      (M14EndpointVariationField V s)

noncomputable def M14VariationEndpointAcceleration
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) (s : ℝ)
    (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    G.Horizontal (R.curve s) :=
  (V.square_base s).symm ▸
    M14HorizontalCovariantDerivative G (fun u => V.squareFamily s u)
      V.parameterDomain (M14EndpointVariationField V s) (D.endpoint_extension s hs) 0

noncomputable def M14FirstVariationBoundaryTerm
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R)) : ℝ :=
  G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt τ₂))
      (M14SquareRootVelocity R (Real.sqrt τ₂)) (M14VariationField V (Real.sqrt τ₂)) -
    G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt τ₁))
      (M14SquareRootVelocity R (Real.sqrt τ₁)) (M14VariationField V (Real.sqrt τ₁))

noncomputable def M14FirstVariationResidualIntegral
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) : ℝ :=
  ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
    -M14SquareRootEulerResidual G R D.base_extension s (M14VariationField V s)

noncomputable def M14SecondVariationBoundaryTerm
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) : ℝ :=
  let h₂ : Real.sqrt τ₂ ∈ M14SqrtParameterInterval τ₁ τ₂ :=
    ⟨Real.sqrt_le_sqrt (le_of_lt p.tau_lt), le_rfl⟩
  let h₁ : Real.sqrt τ₁ ∈ M14SqrtParameterInterval τ₁ τ₂ :=
    ⟨le_rfl, Real.sqrt_le_sqrt (le_of_lt p.tau_lt)⟩
  G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt τ₂))
      (M14SquareRootVelocity R (Real.sqrt τ₂))
      (M14VariationEndpointAcceleration V D (Real.sqrt τ₂) h₂) -
    G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt τ₁))
      (M14SquareRootVelocity R (Real.sqrt τ₁))
      (M14VariationEndpointAcceleration V D (Real.sqrt τ₁) h₁)

noncomputable def M14SecondVariationIndexDensity
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) (s : ℝ) : ℝ :=
  let q := R.curve s
  let A := M14SquareRootVelocity R s
  let Y := M14VariationField V s
  let DY := M14HorizontalCovariantDerivative G R.curve
    (M14SqrtParameterInterval τ₁ τ₂) (M14VariationField V)
    D.variation_extension s
  G.spacetime.horizontalMetric.inner q DY DY +
    horizontalRiemann G.leafwise q Y A A Y +
    2 * s ^ 2 * M14HorizontalHessianPairing G q Y Y -
    4 * s * M14HorizontalRicciDerivativePairing G q Y A Y +
    2 * s * M14HorizontalRicciDerivativePairing G q A Y Y

noncomputable def M14SecondVariationIndexForm
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) : ℝ :=
  ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, M14SecondVariationIndexDensity V D s

def M14VariationJacobiCondition
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) : Prop :=
  ∃ Q : M14JacobiFieldData G R.curve
      (M14SqrtParameterInterval τ₁ τ₂),
    Q.field = M14VariationField V ∧
    HEq Q.extension D.variation_extension ∧
    Q.field (Real.sqrt τ₁) = 0 ∧
    Q.field (Real.sqrt τ₂) = 0 ∧
    (∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      ∀ W : G.Horizontal (R.curve s), M14JacobiResidual G R Q s W = 0)

def M14FirstVariationIdentity
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) : Prop :=
  HasDerivAt (M14VariationAction V)
    (M14FirstVariationBoundaryTerm V + M14FirstVariationResidualIntegral V D) 0

def M14SecondVariationIdentity
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) : Prop :=
  (∃ d₁ : ℝ,
    HasDerivAt (M14VariationAction V) d₁ 0 ∧
      d₁ = M14FirstVariationBoundaryTerm V + M14FirstVariationResidualIntegral V D) ∧
  (∃ d₂ : ℝ,
    HasDerivAt (fun u => deriv (fun v => M14VariationAction V v) u) d₂ 0 ∧
      d₂ = M14SecondVariationBoundaryTerm V D + M14SecondVariationIndexForm V D)

end PoincareConjecture
