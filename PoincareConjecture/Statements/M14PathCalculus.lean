import PoincareConjecture.Definitions.M14PathCalculus

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}
variable {G : GeneralizedLGeometryTransport n X time I}

def M14MinimizerEulerStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y),
    M14IsMinimizing p →
      ∃ E : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂) p.horizontal_velocity,
        M14EulerEquation G p E

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

def M14FirstVariationStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (R : M14SquareRootPath G p)
    (V : M14LVariationData G p R),
    ∃ D : M14VariationDerivativeData V, M14FirstVariationIdentity V D

def M14SecondVariationStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T τ₁ τ₂ : ℝ) (x y : G.Point)
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (R : M14SquareRootPath G p)
    (V : M14LVariationData G p R)
    (E₀ : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂) p.horizontal_velocity),
    M14EulerEquation G p E₀ →
      ∃ D : M14VariationDerivativeData V, M14SecondVariationIdentity V D

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

end PoincareConjecture
