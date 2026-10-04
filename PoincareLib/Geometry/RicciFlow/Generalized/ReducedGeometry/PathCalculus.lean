import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Basic
import PoincareLib.Geometry.Riemannian.Tensor.Operations
import PoincareLib.Geometry.Riemannian.ScalarOperators
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M14PathCalculus.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are unchanged;
imports and module placement are adapted. See
`references/ricci-flow/mapher/generalized-noncollapse-port.json`. -/

/-!
# M14 path calculus on the actual horizontal bundle

The records in this file carry the geometric fields used by the variational
calculus.  In particular, a pullback derivative is built from a genuine
parameter-dependent horizontal extension and `rawHorizontalCovariantDerivative`;
there are no stand-alone scalar residual or Jacobi operator fields.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}
variable {G : GeneralizedLGeometryTransport n X time I}

/-- The closed interval used by the square-root parameter. -/
def M14SqrtParameterInterval (τ₁ τ₂ : ℝ) : Set ℝ :=
  Set.Icc (Real.sqrt τ₁) (Real.sqrt τ₂)

/-- A parameter-dependent local horizontal extension along an actual curve. -/
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

/-- Pullback covariant derivative using the actual horizontal connection. -/
noncomputable def M14HorizontalCovariantDerivative
    (G : GeneralizedLGeometryTransport n X time I)
    (γ : ℝ → G.Point) (J : Set ℝ)
    (Y : ∀ s, G.Horizontal (γ s))
    (E : M14PullbackExtension G γ J Y) (s : ℝ) : G.Horizontal (γ s) :=
  deriv (fun r : ℝ => E.extension r (γ s)) s +
    rawHorizontalCovariantDerivative G.leafwise (E.extension s) (γ s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))

/-- The horizontal differential of scalar curvature on the selected slice. -/
noncomputable def M14HorizontalScalarDifferential
    (G : GeneralizedLGeometryTransport n X time I)
    (p : G.Point) : TangentSpace (spacetimeModel n) p →L[ℝ] ℝ :=
  mvfderiv (spacetimeModel n) (fun q : G.Point =>
    horizontalScalarCurvature G.leafwise q) p

/-- The paired singular Euler residual at a positive backward time. -/
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

/-- The paired Euler equation on the actual interior. -/
def M14EulerEquation
    (G : GeneralizedLGeometryTransport n X time I)
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y)
    (E : M14PullbackExtension G p.curve (Set.Ioo τ₁ τ₂) p.horizontal_velocity) : Prop :=
  ∀ τ ∈ Set.Ioo τ₁ τ₂, ∀ W : G.Horizontal (p.curve τ), M14EulerResidual G p E τ W = 0

/-- A smooth square-root representative with its actual horizontal velocity. -/
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

/-- The actual square-root horizontal velocity `A = 2s X`. -/
noncomputable def M14SquareRootVelocity
    {T τ₁ τ₂ : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T τ₁ τ₂ x y}
    (R : M14SquareRootPath G p) (s : ℝ) : G.Horizontal (R.curve s) :=
  R.horizontal_velocity s

/-- The square-root Euler residual, paired with a horizontal vector. -/
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

/-- Ricci's covariant derivative, transported from the selected slice. -/
noncomputable def M14HorizontalRicciDerivativePairing
    (G : GeneralizedLGeometryTransport n X time I)
    (p : G.Point) (U V W : G.Horizontal p) : ℝ :=
  let t := G.spacetime.timeFunction p
  let x := spacetimeSlicePoint G.slices p
  let j := (G.slices t).tangentEquiv x
  (G.leafwise.sliceConnection t).covariantTensorDerivative
    (G.leafwise.sliceConnection t).ricciEvaluation x ![
      j.symm U, j.symm V, j.symm W]

/-- The connection-time variation tensor paired with the metric. -/
noncomputable def M14BcalPairing
    (G : GeneralizedLGeometryTransport n X time I)
    (p : G.Point) (U V W : G.Horizontal p) : ℝ :=
  M14HorizontalRicciDerivativePairing G p U V W +
    M14HorizontalRicciDerivativePairing G p V U W -
    M14HorizontalRicciDerivativePairing G p W U V

/-- The transported Hessian of scalar curvature. -/
noncomputable def M14HorizontalHessianPairing
    (G : GeneralizedLGeometryTransport n X time I)
    (p : G.Point) (U V : G.Horizontal p) : ℝ :=
  let t := G.spacetime.timeFunction p
  let x := spacetimeSlicePoint G.slices p
  let j := (G.slices t).tangentEquiv x
  LeviCivitaData.hessian (G.leafwise.sliceConnection t)
    (G.leafwise.sliceConnection t).scalarCurvature x (j.symm U) (j.symm V)

/-- A horizontal field with actual first and second pullback derivative data. -/
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

/-- The corrected square-root Jacobi residual, paired with a horizontal vector.
The curvature slots `Y A W A` give `g(R(Y,A)A,W)` in the project's convention. -/
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

end PoincareMT

