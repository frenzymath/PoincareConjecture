import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.PathCalculus

/-! Adapted from Mapher `PoincareMT/Definitions/M14PathCalculus.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}
variable {G : GeneralizedLGeometryTransport n X time I}

/-- A variation of an actual backward path with a square-root representative. -/
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
  /-- Endpoint conditions are recorded as propositions tied to this family. -/
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

/-- The horizontal parameter field of a variation, on the base square curve. -/
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

/-- The endpoint variation field before applying the endpoint connection. -/
noncomputable def M14EndpointVariationField
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R)) (s u : ℝ) :
    G.Horizontal (V.squareFamily s u) :=
  G.spacetime.horizontalProjection (V.squareFamily s u)
    (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n)
      (fun r => V.squareFamily s r) u (1 : ℝ))

/-- The local extensions needed for first and second variation formulas. -/
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

/-- Covariant acceleration of the endpoint variation at a square-root time. -/
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

/-- The first variation boundary contribution. -/
noncomputable def M14FirstVariationBoundaryTerm
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R)) : ℝ :=
  G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt τ₂))
      (M14SquareRootVelocity R (Real.sqrt τ₂)) (M14VariationField V (Real.sqrt τ₂)) -
    G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt τ₁))
      (M14SquareRootVelocity R (Real.sqrt τ₁)) (M14VariationField V (Real.sqrt τ₁))

/-- The integrated paired Euler residual in the first variation. -/
noncomputable def M14FirstVariationResidualIntegral
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) : ℝ :=
  ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
    -M14SquareRootEulerResidual G R D.base_extension s (M14VariationField V s)

/-- The acceleration boundary contribution retained in the general second variation. -/
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

/-- The expanded second-variation index density on actual horizontal fibers. -/
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

/-- The actual index form, with the signed interval integral. -/
noncomputable def M14SecondVariationIndexForm
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) : ℝ :=
  ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, M14SecondVariationIndexDensity V D s

/-! A fixed-endpoint Jacobi witness must use the variation field and the
same first pullback extension as the selected variation derivative data. The
extension types depend on those fields, so their agreement is heterogeneous.
-/
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

/-- The general first-variation identity as a proposition on the actual action. -/
def M14FirstVariationIdentity
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R))
    (D : M14VariationDerivativeData V) : Prop :=
  HasDerivAt (M14VariationAction V)
    (M14FirstVariationBoundaryTerm V + M14FirstVariationResidualIntegral V D) 0

/-- The general second-variation identity, including both endpoint accelerations. -/
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

end PoincareMT
