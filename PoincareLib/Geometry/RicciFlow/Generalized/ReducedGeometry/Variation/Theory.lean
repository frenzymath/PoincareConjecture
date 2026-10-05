import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Basic

/-! Adapted from Mapher `PoincareMT/Statements/M14PathCalculus.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# M14 path-calculus statements

These are the theorem-level contracts for the actual horizontal path records.
They quantify the local extension and variation data explicitly; none of the
statements introduces an unconstrained scalar residual or operator.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}
variable {G : GeneralizedLGeometryTransport n X time I}

/-- A minimizer has an actual horizontal extension satisfying the Euler equation. -/
def M14MinimizerEulerStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y),
    M14IsMinimizing p →
      ∃ E : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂) p.horizontal_velocity,
        M14EulerEquation G p E

/-- A regularized base path has the nonsingular paired Euler expression. -/
def M14SquareRootEulerStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (R : M14SquareRootPath G p),
    M14IsMinimizing p →
    ∃ E : M14PullbackExtension G R.curve
        (M14SqrtParameterInterval τ₁ τ₂) R.horizontal_velocity,
      ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
        ∀ W : G.Horizontal (R.curve s),
        M14SquareRootEulerResidual G R E s W = 0

/-! Morgan--Tian Definition 6.7 and Lemma 6.8 (p. 108) regularize every
Euler path, including nonminimizing ones, by constructing the square-root path.
The conditional `square_root_euler` field below remains useful when a path is
already supplied by another statement. -/
def M14SquareRootRegularizationStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (E₀ : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂) p.horizontal_velocity),
    M14EulerEquation G p E₀ →
    ∃ R : M14SquareRootPath G p,
      ∃ E : M14PullbackExtension G R.curve
          (M14SqrtParameterInterval τ₁ τ₂) R.horizontal_velocity,
        ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
          ∀ W : G.Horizontal (R.curve s),
            M14SquareRootEulerResidual G R E s W = 0

/-- The endpoint restrictions used to distinguish the two variation formulas. -/
def M14InitialEndpointFixed
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R)) : Prop :=
  V.left_endpoint_fixed

def M14BothEndpointsFixed
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    {R : M14SquareRootPath G p}
    (V : M14LVariationData G (p := p) (R := R)) : Prop :=
  M14InitialEndpointFixed V ∧
    V.right_endpoint_fixed

/-- The first variation identity with the actual boundary and Euler terms. -/
def M14FirstVariationStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (R : M14SquareRootPath G p)
    (V : M14LVariationData G p R),
    ∃ D : M14VariationDerivativeData V, M14FirstVariationIdentity V D

/-- The second variation along an Euler path keeps the endpoint acceleration
boundary term; minimality is not required (Proposition 6.33). -/
def M14SecondVariationStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (R : M14SquareRootPath G p)
    (V : M14LVariationData G p R)
    (E₀ : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂) p.horizontal_velocity),
    M14EulerEquation G p E₀ →
      ∃ D : M14VariationDerivativeData V, M14SecondVariationIdentity V D

/-- The index form for a fixed-endpoint variation is the nonnegative second
    variation expression, with the displayed curvature, Hessian, and Ricci
    derivative terms. -/
def M14FixedEndpointIndexStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (R : M14SquareRootPath G p)
    (V : M14LVariationData G p R),
    M14IsMinimizing p → M14BothEndpointsFixed V →
      ∃ D : M14VariationDerivativeData V,
        (∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
          ∀ W : G.Horizontal (R.curve s),
            M14SquareRootEulerResidual G R D.base_extension s W = 0) ∧
        0 ≤ M14SecondVariationIndexForm V D

/-- Morgan--Tian Proposition 6.13 and Lemma 6.14 (pp. 110--112): the
fixed-endpoint index kernel is exactly the corrected Jacobi equation for the
actual variation field, with the endpoint acceleration term removed.
The dependent extension equality ties the witness to the selected derivative
data rather than to an unrelated Jacobi field. -/
def M14FixedEndpointIndexKernelStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (R : M14SquareRootPath G p)
    (V : M14LVariationData G p R),
    M14IsMinimizing p → M14BothEndpointsFixed V →
      ∃ D : M14VariationDerivativeData V,
        M14SecondVariationIdentity V D ∧
        M14SecondVariationBoundaryTerm V D = 0 ∧
        (∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
          ∀ W : G.Horizontal (R.curve s),
            M14SquareRootEulerResidual G R D.base_extension s W = 0) ∧
        0 ≤ M14SecondVariationIndexForm V D ∧
        (M14SecondVariationIndexForm V D = 0 ↔
          M14VariationJacobiCondition V D)

/-- The corrected Jacobi IVP along an Euler path (Lemmas 6.10 and 6.12). -/
def M14JacobiStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (R : M14SquareRootPath G p)
    (W : G.Horizontal (R.curve (Real.sqrt τ₁)))
    (E₀ : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂) p.horizontal_velocity),
    M14EulerEquation G p E₀ →
    ∃ Q : M14JacobiFieldData G R.curve
      (M14SqrtParameterInterval τ₁ τ₂),
      Q.field (Real.sqrt τ₁) = 0 ∧
      M14JacobiFirstDerivative Q (Real.sqrt τ₁) = W ∧
      ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
        ∀ Z : G.Horizontal (R.curve s), M14JacobiResidual G R Q s Z = 0

/-- Initial-zero Jacobi fields are constrained only at the initial endpoint. -/
def M14InitialJacobiStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (R : M14SquareRootPath G p)
    (W : G.Horizontal (R.curve (Real.sqrt τ₁)))
    (E₀ : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂) p.horizontal_velocity),
    M14EulerEquation G p E₀ →
      ∃ Q : M14JacobiFieldData G R.curve
        (M14SqrtParameterInterval τ₁ τ₂),
        Q.field (Real.sqrt τ₁) = 0 ∧
        M14JacobiFirstDerivative Q (Real.sqrt τ₁) = W ∧
        (∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
          ∀ Z : G.Horizontal (R.curve s), M14JacobiResidual G R Q s Z = 0) ∧
        (∀ Q' : M14JacobiFieldData G R.curve
            (M14SqrtParameterInterval τ₁ τ₂),
          Q'.field (Real.sqrt τ₁) = 0 →
          M14JacobiFirstDerivative Q' (Real.sqrt τ₁) = W →
          (∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
            ∀ Z : G.Horizontal (R.curve s), M14JacobiResidual G R Q' s Z = 0) →
          ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, Q'.field s = Q.field s)

/-- The complete calculus contract consumed by the remaining M14 modules. -/
structure M14PathCalculusConclusion
    (G : GeneralizedLGeometryTransport n X time I) : Prop where
  minimizer_euler : M14MinimizerEulerStatement G
  square_root_euler : M14SquareRootEulerStatement G
  square_root_regularization : M14SquareRootRegularizationStatement G
  first_variation : M14FirstVariationStatement G
  second_variation : M14SecondVariationStatement G
  fixed_endpoint_index : M14FixedEndpointIndexStatement G
  fixed_endpoint_index_kernel : M14FixedEndpointIndexKernelStatement G
  jacobi : M14JacobiStatement G
  initial_jacobi : M14InitialJacobiStatement G

end PoincareMT
