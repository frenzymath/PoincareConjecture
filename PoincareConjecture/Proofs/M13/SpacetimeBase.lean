import PoincareConjecture.Proofs.M13.HorizontalBundle
import PoincareConjecture.Proofs.M13.SpacetimeClock
import PoincareConjecture.Proofs.M13.Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

theorem parabolicHorizontalFamily_eq (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (fun p : S.Point ↦ (show Submodule ℝ (SpacetimeModelVector n) from
      spacetimeHorizontal (n := n) S.timeFunction p)) =
    (fun p : S.Point ↦ (show Submodule ℝ (SpacetimeModelVector n) from
      spacetimeHorizontal (n := n)
        (fun q : S.Point ↦ parabolicTime Q a (S.timeFunction q)) p)) := by
  funext p
  exact (parabolicClock_horizontal_eq S Q hQ a p).symm

noncomputable def parabolicHorizontalBundle (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    HorizontalBundleData n S.Point
      (fun p ↦ spacetimeHorizontal (n := n)
        (fun q : S.Point ↦ parabolicTime Q a (S.timeFunction q)) p) :=
  (spacetimeHorizontalBundle S).transport (parabolicHorizontalFamily_eq S Q hQ a)

theorem parabolicHorizontalBundle_projection_val
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : S.Point) (Z : TangentSpace (spacetimeModel n) p) :
    ((parabolicHorizontalBundle S Q hQ a).projection p Z).val =
      (S.horizontalProjection p Z).val :=
  HorizontalBundleData.transport_projection_val (spacetimeHorizontalBundle S)
    (parabolicHorizontalFamily_eq S Q hQ a) p Z

noncomputable def parabolicSpacetime (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    GeneralizedFlowSpacetime n X (fun p ↦ parabolicTime Q a (time p))
      (parabolicInterval Q hQ a I) := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) X :=
    S.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ X := S.isManifold
  let B := parabolicHorizontalBundle S Q hQ a
  letI := B.topology
  letI := B.fiberBundle
  letI := B.vectorBundle
  letI := B.smoothBundle
  let g := scaleSmoothMetric B.metric Q hQ
  refine {
    chartedSpace := S.chartedSpace
    isManifold := S.isManifold
    t2Space := S.t2Space
    t3Space := S.t3Space
    secondCountable := S.secondCountable
    time_smooth := parabolicClock_smooth S Q a
    time_range := parabolicClock_range S Q hQ a
    boundary_eq := parabolicClock_boundary S Q hQ a
    timeVector := fun p ↦ (1 / Q : ℝ) • S.timeVector p
    timeVector_smooth := parabolicTimeVector_smooth S Q
    timeVector_normalized := parabolicTimeVector_normalized S Q hQ a
    horizontalTopology := B.topology
    horizontalFiberBundle := B.fiberBundle
    horizontalVectorBundle := B.vectorBundle
    horizontalSmoothBundle := B.smoothBundle
    horizontal_inclusion_smooth := B.inclusion_smooth
    horizontalProjection := B.projection
    horizontalProjection_eq := ?_
    horizontalProjection_identity := B.projection_identity
    tangent_decomposition := ?_
    horizontalProjection_smooth := B.projection_smooth
    metric := g }
  · intro p Z
    exact (parabolicHorizontalBundle_projection_val S Q hQ a p Z).trans
      (parabolicClock_projection_formula S Q hQ a p Z).symm
  · intro p Z
    have hp := (parabolicHorizontalBundle_projection_val S Q hQ a p Z).trans
      (parabolicClock_projection_formula S Q hQ a p Z).symm
    exact (sub_eq_iff_eq_add').1 hp.symm

theorem parabolicSpacetime_chartedSpace (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (parabolicSpacetime S Q hQ a).chartedSpace = S.chartedSpace := rfl

theorem parabolicSpacetime_timeVector (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (p : S.Point) :
    (show SpacetimeModelVector n from (parabolicSpacetime S Q hQ a).timeVector p) =
      (1 / Q : ℝ) • S.timeVector p := rfl

noncomputable def parabolicSpacetimeHorizontal
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : S.Point) : S.Horizontal p ≃L[ℝ] (parabolicSpacetime S Q hQ a).Horizontal p :=
  HorizontalBundleData.fiberEquiv (parabolicHorizontalFamily_eq S Q hQ a) p

theorem parabolicSpacetimeHorizontal_val
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : S.Point) (v : S.Horizontal p) :
    (show SpacetimeModelVector n from (parabolicSpacetimeHorizontal S Q hQ a p v).val) =
      v.val := rfl

theorem parabolicSpacetimeHorizontal_smooth
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) S.Horizontal ↦
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := (parabolicSpacetime S Q hQ a).Horizontal) v.proj
          (parabolicSpacetimeHorizontal S Q hQ a v.proj v.2)) :=
  HorizontalBundleData.transport_smooth (spacetimeHorizontalBundle S)
    (parabolicHorizontalFamily_eq S Q hQ a)

theorem parabolicSpacetimeHorizontal_inverse_smooth
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n))
          (parabolicSpacetime S Q hQ a).Horizontal ↦
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := S.Horizontal) v.proj
          ((parabolicSpacetimeHorizontal S Q hQ a v.proj).symm v.2)) :=
  HorizontalBundleData.transport_inverse_smooth (spacetimeHorizontalBundle S)
    (parabolicHorizontalFamily_eq S Q hQ a)

theorem parabolicSpacetime_projection
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : S.Point) (Z : TangentSpace (spacetimeModel n) p) :
    (parabolicSpacetime S Q hQ a).horizontalProjection p Z =
      parabolicSpacetimeHorizontal S Q hQ a p (S.horizontalProjection p Z) :=
  HorizontalBundleData.transport_projection (spacetimeHorizontalBundle S)
    (parabolicHorizontalFamily_eq S Q hQ a) p Z

theorem parabolicSpacetime_metric
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : S.Point) (v w : S.Horizontal p) :
    (parabolicSpacetime S Q hQ a).horizontalMetric.inner p
      (parabolicSpacetimeHorizontal S Q hQ a p v)
      (parabolicSpacetimeHorizontal S Q hQ a p w) =
        Q * S.horizontalMetric.inner p v w :=
  congrArg (Q * ·) (HorizontalBundleData.transport_metric (spacetimeHorizontalBundle S)
    (parabolicHorizontalFamily_eq S Q hQ a) p v w)

noncomputable def parabolicSpacetimeIdentification
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    Diffeomorph (spacetimeModel n) (spacetimeModel n)
      S.Point (parabolicSpacetime S Q hQ a).Point ∞ :=
  Diffeomorph.refl (spacetimeModel n) S.Point ∞

theorem parabolicSpacetimeIdentification_eq
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : S.Point) : parabolicSpacetimeIdentification S Q hQ a p = p := rfl

theorem parabolicSpacetimeIdentification_derivative
    (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : S.Point) (Z : TangentSpace (spacetimeModel n) p) :
    (show SpacetimeModelVector n from
      mfderiv (spacetimeModel n) (spacetimeModel n)
        (parabolicSpacetimeIdentification S Q hQ a) p Z) = Z := by
  change mfderiv (spacetimeModel n) (spacetimeModel n) (@id S.Point) p Z = Z
  rw [mfderiv_id]
  rfl

end PoincareConjecture.M13
