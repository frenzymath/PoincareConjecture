import PoincareConjecture.Proofs.M14.Sec6_4_GaugeTensorDerivatives
import PoincareConjecture.Statements.M14GeneralizedLGeometry

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {K : SpacetimeInterval} {J : SmoothSpacetimeInterval K}
  {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge G.spacetime J C}
  {g : MovingSpacetimeGaugeGeometry e}

theorem movingGauge_spacetimeDifferential (t : J.Point) (x : C) (f : G.Point → ℝ)
    (hf : ContMDiffAt (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ f (e.toSpacetime (t, x)))
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => f (e.toSpacetime (t, y))) x v =
      mvfderiv (spacetimeModel n) f (e.toSpacetime (t, x))
        (g.spatialTangentEquiv t x v).val := by
  have he : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun y : C => e.toSpacetime (t, y)) :=
    e.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  change mvfderiv (𝓡 n) (f ∘ (fun y : C => e.toSpacetime (t, y))) x v = _
  rw [mvfderiv_comp_apply x (hf.mdifferentiableAt (by simp))
    (he.mdifferentiable (by simp) x), ← g.spatialTangentEquiv_eq]

theorem sliceHessian_eq_reducedLengthHessianPairing {t T τ : ℝ} (ht : t = T - τ)
    (q : G.Point) (hq : G.spacetime.timeFunction q = t) (f : G.Point → ℝ)
    (v w : G.Horizontal q) :
    (G.leafwise.sliceConnection t).hessian (fun r => f r.val) ⟨q, hq⟩
        (((G.slices t).tangentEquiv ⟨q, hq⟩).symm v)
        (((G.slices t).tangentEquiv ⟨q, hq⟩).symm w) =
      M14ReducedLengthHessianPairing G ⟨q, hq.trans ht⟩ f v w := by
  subst t
  rfl

theorem movingGauge_spacetimeHessian {c : MetricLeviCivitaFamily g.metric}
    (H : MovingGaugeCalculus G.leafwise g c) (t : J.Point) (x : C)
    {T τ : ℝ} (ht : t.val = T - τ) (f : G.Point → ℝ)
    (hf : ContMDiffAt (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ f (e.toSpacetime (t, x)))
    (v w : TangentSpace (𝓡 n) x) :
    (c t.val).hessian (fun y => f (e.toSpacetime (t, y))) x v w =
      M14ReducedLengthHessianPairing G
        (⟨e.toSpacetime (t, x), (e.time_eq (t, x)).trans ht⟩ : (G.slices (T - τ)).Point)
        f (g.spatialTangentEquiv t x v) (g.spatialTangentEquiv t x w) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (G.slices t.val).Point :=
    (G.slices t.val).chartedSpace
  let F := movingGaugeSliceMap e G.slices t
  let D := G.leafwise.sliceConnection t.val
  have hi : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (Subtype.val : (G.slices t.val).Point → G.Point) :=
    (G.slices t.val).inclusion_smooth
  have hf' : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun q : (G.slices t.val).Point => f q.val) (F x) := hf.comp (F x) (hi (F x))
  have hinv (y : C) : (mfderiv (𝓡 n) (𝓡 n) F y).IsInvertible := by
    rw [← (H.slice_localDiffeomorph t).mfderivToContinuousLinearEquiv_coe (by simp) y]
    exact ContinuousLinearMap.isInvertible_equiv
  have hh := (c t.val).hessian_comp_of_metric_pullback D
    ((H.slice_localDiffeomorph t).contMDiff x) (Eventually.of_forall hinv)
    (Eventually.of_forall (fun y a b => (H.slice_metric_eq t y a b).symm)) hf' v w
  have hv (a : TangentSpace (𝓡 n) x) :
      ((G.slices t.val).tangentEquiv (F x)).symm (g.spatialTangentEquiv t x a) =
        mfderiv (𝓡 n) (𝓡 n) F x a := by
    rw [← H.slice_tangent_eq t x a]
    exact ContinuousLinearEquiv.symm_apply_apply _ _
  have hactual : (c t.val).hessian (fun y => f (e.toSpacetime (t, y))) x v w =
      D.hessian (fun q => f q.val) (F x)
        (((G.slices t.val).tangentEquiv (F x)).symm (g.spatialTangentEquiv t x v))
        (((G.slices t.val).tangentEquiv (F x)).symm (g.spatialTangentEquiv t x w)) := by
    rw [hv v, hv w]
    exact hh
  exact hactual.trans (sliceHessian_eq_reducedLengthHessianPairing ht
    (F x).val (F x).property f (g.spatialTangentEquiv t x v) (g.spatialTangentEquiv t x w))

end PoincareConjecture.M14
