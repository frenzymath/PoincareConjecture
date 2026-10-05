import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.Hessian.HorizontalHessianTrace
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Tensor.RicciContractions

/-!
# The scalar trace in actual horizontal orthonormal coordinates

The selected slice tangent equivalence is an isometry. Transporting
an actual horizontal orthonormal basis therefore computes the same
Ricci trace as the selected slice connection. Morgan-Tian
Proposition 6.81, equation (6.19), p. 145.
-/

set_option autoImplicit false
-- Slice tangent fibers use the specified metric renorming on their actual model.
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- An actual horizontal orthonormal basis computes horizontal scalar
curvature by the Ricci trace, Proposition 6.81, equation (6.19), p. 145. -/
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

end PoincareMT.M14
