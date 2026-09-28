import PoincareConjecture.Definitions.M11TimeInterval
import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.LocalDiffeomorph










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture


noncomputable abbrev spacetimeModel (n : ℕ) := (𝓡∂ 1).prod (𝓡 n)


abbrev SpacetimeModelVector (n : ℕ) :=
  EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)


noncomputable def spacetimeHorizontal {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) X]
    (time : X → ℝ) (p : X) : Submodule ℝ (TangentSpace (spacetimeModel n) p) :=
  (mfderiv (spacetimeModel n) 𝓘(ℝ) time p).toLinearMap.ker


abbrev spacetimeSlice {X : Type u} (time : X → ℝ) (t : ℝ) :=
  {p : X // time p = t}




structure GeneralizedFlowSpacetime (n : ℕ) (X : Type u) [TopologicalSpace X]
    (time : X → ℝ) (I : SpacetimeInterval) where
  chartedSpace : ChartedSpace
    (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) X
  isManifold : IsManifold (spacetimeModel n) ∞ X
  t2Space : T2Space X
  t3Space : T3Space X
  secondCountable : SecondCountableTopology X
  time_smooth : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ time
  time_range : Set.range time = I.domain
  boundary_eq : (spacetimeModel n).boundary X = {p | time p ∈ frontier I.domain}
  timeVector : ∀ p : X, TangentSpace (spacetimeModel n) p
  timeVector_smooth : ContMDiff (spacetimeModel n)
    ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
    (fun p : X ↦ Bundle.TotalSpace.mk' (SpacetimeModelVector n)
      (E := (TangentSpace (spacetimeModel n) : X → Type _)) p (timeVector p))
  timeVector_normalized : ∀ p,
    mfderiv (spacetimeModel n) 𝓘(ℝ) time p (timeVector p) = 1
  horizontalTopology : TopologicalSpace
    (Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) (fun p ↦ spacetimeHorizontal (n := n) time p))
  horizontalFiberBundle : FiberBundle (EuclideanSpace ℝ (Fin n))
    (fun p ↦ spacetimeHorizontal (n := n) time p)
  horizontalVectorBundle : VectorBundle ℝ (EuclideanSpace ℝ (Fin n))
    (fun p ↦ spacetimeHorizontal (n := n) time p)
  horizontalSmoothBundle : ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin n))
    (fun p ↦ spacetimeHorizontal (n := n) time p) (spacetimeModel n)
  horizontal_inclusion_smooth :
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n))
        (fun p ↦ spacetimeHorizontal (n := n) time p) ↦
        Bundle.TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : X → Type _)) v.proj v.2.val)
  horizontalProjection : ∀ p, TangentSpace (spacetimeModel n) p →L[ℝ]
    spacetimeHorizontal (n := n) time p
  horizontalProjection_eq : ∀ p v,
    (horizontalProjection p v).val =
      v - (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) time p v) • timeVector p
  horizontalProjection_identity : ∀ p (v : spacetimeHorizontal (n := n) time p),
    horizontalProjection p v.val = v
  tangent_decomposition : ∀ p v,
    v = (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) time p v) • timeVector p +
      (horizontalProjection p v).val
  horizontalProjection_smooth :
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) X ↦
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := fun p ↦ spacetimeHorizontal (n := n) time p) v.proj
          (horizontalProjection v.proj v.2))
  metric : Bundle.ContMDiffRiemannianMetric (spacetimeModel n) ∞
    (EuclideanSpace ℝ (Fin n)) (fun p ↦ spacetimeHorizontal (n := n) time p)

namespace GeneralizedFlowSpacetime

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}


abbrev Point (_F : GeneralizedFlowSpacetime n X time I) := X

instance (F : GeneralizedFlowSpacetime n X time I) :
    ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) F.Point :=
  F.chartedSpace

instance (F : GeneralizedFlowSpacetime n X time I) :
    IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold

instance (F : GeneralizedFlowSpacetime n X time I) : T2Space F.Point := F.t2Space

instance (F : GeneralizedFlowSpacetime n X time I) : T3Space F.Point := F.t3Space

instance (F : GeneralizedFlowSpacetime n X time I) :
    SecondCountableTopology F.Point := F.secondCountable


def timeFunction (F : GeneralizedFlowSpacetime n X time I) : F.Point → ℝ := time


noncomputable abbrev Horizontal (F : GeneralizedFlowSpacetime n X time I)
    (p : F.Point) : Type := spacetimeHorizontal (n := n) F.timeFunction p

instance (F : GeneralizedFlowSpacetime n X time I) : TopologicalSpace
    (Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) F.Horizontal) := F.horizontalTopology

instance (F : GeneralizedFlowSpacetime n X time I) :
    FiberBundle (EuclideanSpace ℝ (Fin n)) F.Horizontal := F.horizontalFiberBundle

instance (F : GeneralizedFlowSpacetime n X time I) :
    VectorBundle ℝ (EuclideanSpace ℝ (Fin n)) F.Horizontal := F.horizontalVectorBundle

instance (F : GeneralizedFlowSpacetime n X time I) :
    ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin n)) F.Horizontal (spacetimeModel n) :=
  F.horizontalSmoothBundle


noncomputable abbrev horizontalMetric (F : GeneralizedFlowSpacetime n X time I) :
    Bundle.ContMDiffRiemannianMetric (B := F.Point) (spacetimeModel n) ∞
      (EuclideanSpace ℝ (Fin n)) F.Horizontal := F.metric


abbrev Slice (F : GeneralizedFlowSpacetime n X time I) (t : ℝ) :=
  spacetimeSlice F.timeFunction t

end GeneralizedFlowSpacetime

end PoincareConjecture
