import PoincareLib.Geometry.Spacetime.Slice
import PoincareLib.Geometry.Riemannian.Curvature.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M12HorizontalCalculus.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# Raw horizontal calculus on the selected spacetime

Morgan-Tian Definition 3.36 and Remark 3.37, pp. 60-61, with the connection
and curvature conventions of pp. 3-7. The horizontal Lie expression uses
fixed bundle extensions and the actual manifold Lie bracket. Curvature is
transported from retained slice connections through the actual differential
of slice inclusion. Tensoriality, regularity, and connection laws are M12
theorem conclusions, not proof fields in these definitions.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-- A section of the literal horizontal kernel for this spacetime witness. -/
abbrev HorizontalSection (F : GeneralizedFlowSpacetime n X time I) :=
  (p : F.Point) → F.Horizontal p

/-- The actual tangent vector field underlying a horizontal section. -/
def horizontalSectionVectorField (F : GeneralizedFlowSpacetime n X time I)
    (V : HorizontalSection F) (p : F.Point) : TangentSpace (spacetimeModel n) p :=
  (V p).val

/-- Smoothness of a horizontal section on its specified domain. -/
def IsSmoothHorizontalSectionOn (F : GeneralizedFlowSpacetime n X time I)
    (V : HorizontalSection F) (U : Set F.Point) : Prop :=
  ContMDiffOn (spacetimeModel n)
    ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
    (fun p : F.Point ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
      (E := F.Horizontal) p (V p)) U

/-- Raw covariant tensor evaluations on the actual horizontal fibers. -/
abbrev HorizontalCovariantTensorEvaluation (F : GeneralizedFlowSpacetime n X time I)
    (k : ℕ) :=
  (p : F.Point) → (Fin k → F.Horizontal p) → ℝ

/-- Pointwise multilinearity and smooth evaluation on arbitrary local smooth sections. -/
def IsSmoothHorizontalCovariantTensor (F : GeneralizedFlowSpacetime n X time I)
    {k : ℕ} (T : HorizontalCovariantTensorEvaluation F k) : Prop :=
  (∀ p : F.Point, ∃ A : MultilinearMap ℝ (fun _ : Fin k ↦ F.Horizontal p) ℝ,
    ∀ v, T p v = A v) ∧
  ∀ U : Set F.Point, IsOpen U →
    ∀ V : Fin k → HorizontalSection F,
      (∀ i, IsSmoothHorizontalSectionOn F (V i) U) →
      ContMDiffOn (spacetimeModel n) 𝓘(ℝ) ∞ (fun p ↦ T p (fun i ↦ V i p)) U

/-- The projected actual bracket with the normalized time vector. -/
noncomputable def horizontalTimeBracket (F : GeneralizedFlowSpacetime n X time I)
    (V : HorizontalSection F) (p : F.Point) : F.Horizontal p :=
  F.horizontalProjection p
    (VectorField.mlieBracket (spacetimeModel n)
      (show (q : F.Point) → TangentSpace (spacetimeModel n) q from F.timeVector)
      (horizontalSectionVectorField F V) p)

/-- The horizontal metric Lie expression on supplied sections. Its geometric
interpretation requires regularity near the evaluation point. -/
noncomputable def horizontalMetricLieDerivativeOnFields
    (F : GeneralizedFlowSpacetime n X time I)
    (U V : HorizontalSection F) (p : F.Point) : ℝ :=
  mvfderiv (spacetimeModel n)
      (fun q : F.Point ↦ F.horizontalMetric.inner q (U q) (V q)) p (F.timeVector p) -
    F.horizontalMetric.inner p (horizontalTimeBracket F U p) (V p) -
    F.horizontalMetric.inner p (U p) (horizontalTimeBracket F V p)

/-- The pointwise Lie expression, using the fixed local bundle extensions. -/
noncomputable def horizontalMetricLieDerivative
    (F : GeneralizedFlowSpacetime n X time I)
    (p : F.Point) (u v : F.Horizontal p) : ℝ :=
  let U : HorizontalSection F := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let V : HorizontalSection F := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  horizontalMetricLieDerivativeOnFields F U V p

/-- Retained actual Levi-Civita connections for the selected actual slice metrics.
Their existence and joint leafwise regularity are separate theorem conclusions. -/
structure LeafwiseLeviCivitaFamily (F : GeneralizedFlowSpacetime n X time I)
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) where
  sliceConnection : ∀ t : ℝ, LeviCivitaData (S t).metricOnPoints

variable {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

/-- A spacetime point regarded as a point of its exact selected time slice. -/
def spacetimeSlicePoint (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (p : F.Point) :
    (S (F.timeFunction p)).Point :=
  ⟨p, rfl⟩

/-- Restrict a horizontal section through the inverse actual slice differential. -/
noncomputable def restrictHorizontalSection
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (t : ℝ) (V : HorizontalSection F) :
    (x : (S t).Point) → TangentSpace (𝓡 n) x :=
  fun x ↦ ((S t).tangentEquiv x).symm (V x.val)

/-- Four-covariant horizontal curvature, with last-slot convention `g(R(u,v)z,w)`. -/
noncomputable def horizontalRiemann (D : LeafwiseLeviCivitaFamily F S)
    (p : F.Point) (u v w z : F.Horizontal p) : ℝ :=
  let t := F.timeFunction p
  let x : (S t).Point := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  (D.sliceConnection t).curvatureTensor x (j.symm u) (j.symm v) (j.symm w) (j.symm z)

/-- Actual Ricci curvature of the selected slice, transported to its horizontal fiber. -/
noncomputable def horizontalRicci (D : LeafwiseLeviCivitaFamily F S)
    (p : F.Point) (u v : F.Horizontal p) : ℝ :=
  let t := F.timeFunction p
  let x : (S t).Point := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  (D.sliceConnection t).ricci x (j.symm u) (j.symm v)

/-- The scalar curvature of the selected actual time slice. -/
noncomputable def horizontalScalarCurvature (D : LeafwiseLeviCivitaFamily F S)
    (p : F.Point) : ℝ :=
  (D.sliceConnection (F.timeFunction p)).scalarCurvature (spacetimeSlicePoint S p)

/-- The full four-tensor norm of the selected actual time slice. -/
noncomputable def horizontalCurvatureNorm (D : LeafwiseLeviCivitaFamily F S)
    (p : F.Point) : ℝ :=
  (D.sliceConnection (F.timeFunction p)).curvatureTensorNorm (spacetimeSlicePoint S p)

/-- The squared full curvature norm; smoothness at curvature zero concerns this square. -/
noncomputable def horizontalCurvatureNormSq (D : LeafwiseLeviCivitaFamily F S)
    (p : F.Point) : ℝ :=
  horizontalCurvatureNorm D p ^ 2

/-- The intrinsic generalized Ricci equation on the actual horizontal bundle. -/
def IntrinsicGeneralizedRicciEquation (D : LeafwiseLeviCivitaFamily F S) : Prop :=
  ∀ p : F.Point, ∀ u v : F.Horizontal p,
    horizontalMetricLieDerivative F p u v = -2 * horizontalRicci D p u v

/-- The slice covariant derivative transported as a continuous linear map on H. -/
noncomputable def rawLeafwiseCovariantDerivative (D : LeafwiseLeviCivitaFamily F S)
    (V : HorizontalSection F) (p : F.Point) : F.Horizontal p →L[ℝ] F.Horizontal p :=
  let t := F.timeFunction p
  let x : (S t).Point := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  j.toContinuousLinearMap.comp
    (((D.sliceConnection t).connection (restrictHorizontalSection S t V) x).comp
      j.symm.toContinuousLinearMap)

/-- The canonical raw derivative: spatial Levi-Civita derivative plus the time bracket.
Its metric defect on regular sections is dt(Z) times the metric Lie derivative. -/
noncomputable def rawHorizontalCovariantDerivative (D : LeafwiseLeviCivitaFamily F S)
    (V : HorizontalSection F) (p : F.Point) :
    TangentSpace (spacetimeModel n) p →L[ℝ] F.Horizontal p :=
  (rawLeafwiseCovariantDerivative D V p).comp (F.horizontalProjection p) +
    (show TangentSpace (spacetimeModel n) p →L[ℝ] ℝ from
      mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p).smulRight
        (horizontalTimeBracket F V p)

end PoincareMT
