import PoincareConjecture.Proofs.M14.Sec6_5_HorizontalHessianTrace
import PoincareConjecture.Proofs.M09.RicciContractions

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem horizontalRicci_orthonormal_trace (hM04 : RicciFlowCurvatureTheory.{u})
    (q : G.Point) (b : Module.Basis (Fin n) ℝ (G.Horizontal q))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner q (b i) (b j) =
      if i = j then 1 else 0) :
    (∑ i, horizontalRicci G.leafwise q (b i) (b i)) =
      horizontalScalarCurvature G.leafwise q := by
  let S := G.slices (G.spacetime.timeFunction q)
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) S.Point := S.chartedSpace
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : S.Point → Type _) :=
    ⟨S.metricOnPoints.toRiemannianMetric⟩
  let qs := spacetimeSlicePoint G.slices q
  let j := S.tangentEquiv qs
  let bs := b.map j.symm.toLinearEquiv
  have hbs : Orthonormal ℝ bs := by
    apply orthonormal_iff_ite.mpr
    intro i k
    change S.metricOnPoints.inner qs (bs i) (bs k) = _
    rw [S.metric_eq]
    simpa only [bs, j, S, qs, spacetimeSlicePoint, Module.Basis.map_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.apply_symm_apply] using hb i k
  have h := Proofs.M09.ricci_orthonormal_trace hM04
    (G.leafwise.sliceConnection (G.spacetime.timeFunction q)) qs (bs.toOrthonormalBasis hbs)
  simpa only [Module.Basis.coe_toOrthonormalBasis, bs, j, S, qs, spacetimeSlicePoint,
    Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    horizontalRicci, horizontalScalarCurvature] using h

end PoincareConjecture.M14
