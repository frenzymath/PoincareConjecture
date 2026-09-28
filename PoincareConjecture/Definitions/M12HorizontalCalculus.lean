import PoincareConjecture.Definitions.M11SpacetimeSlices
import PoincareConjecture.Definitions.Ch01.Curvature
import Mathlib.LinearAlgebra.Multilinear.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

abbrev HorizontalSection (F : GeneralizedFlowSpacetime n X time I) :=
  (p : F.Point) → F.Horizontal p

def horizontalSectionVectorField (F : GeneralizedFlowSpacetime n X time I)
    (V : HorizontalSection F) (p : F.Point) : TangentSpace (spacetimeModel n) p :=
  (V p).val

def IsSmoothHorizontalSectionOn (F : GeneralizedFlowSpacetime n X time I)
    (V : HorizontalSection F) (U : Set F.Point) : Prop :=
  ContMDiffOn (spacetimeModel n)
    ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
    (fun p : F.Point ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
      (E := F.Horizontal) p (V p)) U

abbrev HorizontalCovariantTensorEvaluation (F : GeneralizedFlowSpacetime n X time I)
    (k : ℕ) :=
  (p : F.Point) → (Fin k → F.Horizontal p) → ℝ

def IsSmoothHorizontalCovariantTensor (F : GeneralizedFlowSpacetime n X time I)
    {k : ℕ} (T : HorizontalCovariantTensorEvaluation F k) : Prop :=
  (∀ p : F.Point, ∃ A : MultilinearMap ℝ (fun _ : Fin k ↦ F.Horizontal p) ℝ,
    ∀ v, T p v = A v) ∧
  ∀ U : Set F.Point, IsOpen U →
    ∀ V : Fin k → HorizontalSection F,
      (∀ i, IsSmoothHorizontalSectionOn F (V i) U) →
      ContMDiffOn (spacetimeModel n) 𝓘(ℝ) ∞ (fun p ↦ T p (fun i ↦ V i p)) U

noncomputable def horizontalTimeBracket (F : GeneralizedFlowSpacetime n X time I)
    (V : HorizontalSection F) (p : F.Point) : F.Horizontal p :=
  F.horizontalProjection p
    (VectorField.mlieBracket (spacetimeModel n)
      (show (q : F.Point) → TangentSpace (spacetimeModel n) q from F.timeVector)
      (horizontalSectionVectorField F V) p)

noncomputable def horizontalMetricLieDerivativeOnFields
    (F : GeneralizedFlowSpacetime n X time I)
    (U V : HorizontalSection F) (p : F.Point) : ℝ :=
  mvfderiv (spacetimeModel n)
      (fun q : F.Point ↦ F.horizontalMetric.inner q (U q) (V q)) p (F.timeVector p) -
    F.horizontalMetric.inner p (horizontalTimeBracket F U p) (V p) -
    F.horizontalMetric.inner p (U p) (horizontalTimeBracket F V p)

noncomputable def horizontalMetricLieDerivative
    (F : GeneralizedFlowSpacetime n X time I)
    (p : F.Point) (u v : F.Horizontal p) : ℝ :=
  let U : HorizontalSection F := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let V : HorizontalSection F := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  horizontalMetricLieDerivativeOnFields F U V p

structure LeafwiseLeviCivitaFamily (F : GeneralizedFlowSpacetime n X time I)
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) where
  sliceConnection : ∀ t : ℝ, LeviCivitaData (S t).metricOnPoints

variable {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

def spacetimeSlicePoint (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (p : F.Point) :
    (S (F.timeFunction p)).Point :=
  ⟨p, rfl⟩

noncomputable def restrictHorizontalSection
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (t : ℝ) (V : HorizontalSection F) :
    (x : (S t).Point) → TangentSpace (𝓡 n) x :=
  fun x ↦ ((S t).tangentEquiv x).symm (V x.val)

noncomputable def horizontalRiemann (D : LeafwiseLeviCivitaFamily F S)
    (p : F.Point) (u v w z : F.Horizontal p) : ℝ :=
  let t := F.timeFunction p
  let x : (S t).Point := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  (D.sliceConnection t).curvatureTensor x (j.symm u) (j.symm v) (j.symm w) (j.symm z)

noncomputable def horizontalRicci (D : LeafwiseLeviCivitaFamily F S)
    (p : F.Point) (u v : F.Horizontal p) : ℝ :=
  let t := F.timeFunction p
  let x : (S t).Point := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  (D.sliceConnection t).ricci x (j.symm u) (j.symm v)

noncomputable def horizontalScalarCurvature (D : LeafwiseLeviCivitaFamily F S)
    (p : F.Point) : ℝ :=
  (D.sliceConnection (F.timeFunction p)).scalarCurvature (spacetimeSlicePoint S p)

noncomputable def horizontalCurvatureNorm (D : LeafwiseLeviCivitaFamily F S)
    (p : F.Point) : ℝ :=
  (D.sliceConnection (F.timeFunction p)).curvatureTensorNorm (spacetimeSlicePoint S p)

noncomputable def horizontalCurvatureNormSq (D : LeafwiseLeviCivitaFamily F S)
    (p : F.Point) : ℝ :=
  horizontalCurvatureNorm D p ^ 2

def IntrinsicGeneralizedRicciEquation (D : LeafwiseLeviCivitaFamily F S) : Prop :=
  ∀ p : F.Point, ∀ u v : F.Horizontal p,
    horizontalMetricLieDerivative F p u v = -2 * horizontalRicci D p u v

noncomputable def rawLeafwiseCovariantDerivative (D : LeafwiseLeviCivitaFamily F S)
    (V : HorizontalSection F) (p : F.Point) : F.Horizontal p →L[ℝ] F.Horizontal p :=
  let t := F.timeFunction p
  let x : (S t).Point := spacetimeSlicePoint S p
  let j := (S t).tangentEquiv x
  j.toContinuousLinearMap.comp
    (((D.sliceConnection t).connection (restrictHorizontalSection S t V) x).comp
      j.symm.toContinuousLinearMap)

noncomputable def rawHorizontalCovariantDerivative (D : LeafwiseLeviCivitaFamily F S)
    (V : HorizontalSection F) (p : F.Point) :
    TangentSpace (spacetimeModel n) p →L[ℝ] F.Horizontal p :=
  (rawLeafwiseCovariantDerivative D V p).comp (F.horizontalProjection p) +
    (show TangentSpace (spacetimeModel n) p →L[ℝ] ℝ from
      mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p).smulRight
        (horizontalTimeBracket F V p)

end PoincareConjecture
