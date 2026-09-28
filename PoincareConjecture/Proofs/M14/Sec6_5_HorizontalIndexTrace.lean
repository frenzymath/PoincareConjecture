import PoincareConjecture.Proofs.M14.Sec6_5_AdaptedIndexTrace
import PoincareConjecture.Proofs.M14.Sec6_4_IndexPair

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  (R : M14SquareRootPath G p)

theorem horizontalIndexPairDensity_eq_slice (s : ℝ)
    (Y W : G.Horizontal (R.curve s)) :
    let q := spacetimeSlicePoint G.slices (R.curve s)
    let D := G.leafwise.sliceConnection (G.spacetime.timeFunction (R.curve s))
    let j := (G.slices (G.spacetime.timeFunction (R.curve s))).tangentEquiv q
    horizontalIndexPairDensity R s Y Y W W =
      sliceIndexDensity D q s (j.symm (R.horizontal_velocity s)) (j.symm Y) (j.symm W) := by
  let q := spacetimeSlicePoint G.slices (R.curve s)
  let S := G.slices (G.spacetime.timeFunction (R.curve s))
  let D := G.leafwise.sliceConnection (G.spacetime.timeFunction (R.curve s))
  let j := S.tangentEquiv q
  have hm := S.metric_eq q (j.symm W) (j.symm W)
  dsimp only [j, S, q, spacetimeSlicePoint] at hm
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hm
  have hR := D.curvatureTensor_swap_last q (j.symm Y) (j.symm (R.horizontal_velocity s))
    (j.symm Y) (j.symm (R.horizontal_velocity s))
  unfold horizontalIndexPairDensity sliceIndexDensity
  simp only [M14BcalPairing, add_sub_cancel_right]
  change G.spacetime.horizontalMetric.inner (R.curve s) W W -
      D.curvatureTensor q (j.symm Y) (j.symm (R.horizontal_velocity s))
        (j.symm Y) (j.symm (R.horizontal_velocity s)) +
      2 * s * ricciDerivativePairing D q (j.symm (R.horizontal_velocity s)) (j.symm Y)
        (j.symm Y) + 2 * s ^ 2 * D.hessian D.scalarCurvature q (j.symm Y) (j.symm Y) -
      4 * s * ricciDerivativePairing D q (j.symm Y) (j.symm (R.horizontal_velocity s))
        (j.symm Y) = _
  rw [hR]
  change _ = S.metricOnPoints.inner q (j.symm W) (j.symm W) + _ + _ - _ + _
  dsimp only [D, j, S, q, spacetimeSlicePoint]
  rw [hm]
  ring

theorem horizontalIndexPairDensity_adapted_trace
    (hM04 : RicciFlowCurvatureTheory.{u}) (s : ℝ)
    (e : Module.Basis (Fin n) ℝ (G.Horizontal (R.curve s)))
    (he : ∀ i j, G.spacetime.horizontalMetric.inner (R.curve s) (e i) (e j) =
      if i = j then 1 else 0) (f fp : ℝ)
    (W : Fin n → G.Horizontal (R.curve s))
    (hW : ∀ i v, G.spacetime.horizontalMetric.inner (R.curve s) (W i) v =
      fp * G.spacetime.horizontalMetric.inner (R.curve s) (e i) v -
        2 * s * f * horizontalRicci G.leafwise (R.curve s) (e i) v) :
    let q := spacetimeSlicePoint G.slices (R.curve s)
    let D := G.leafwise.sliceConnection (G.spacetime.timeFunction (R.curve s))
    (∑ i, horizontalIndexPairDensity R s (f • e i) (f • e i) (W i) (W i)) =
      (n : ℝ) * fp ^ 2 - 4 * s * f * fp * horizontalScalarCurvature G.leafwise (R.curve s) +
        f ^ 2 * (4 * s ^ 2 * D.ricciNormSq q +
          2 * s ^ 2 * D.laplacian D.scalarCurvature q -
            horizontalRicci G.leafwise (R.curve s) (R.horizontal_velocity s)
              (R.horizontal_velocity s)) := by
  let S := G.slices (G.spacetime.timeFunction (R.curve s))
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) S.Point := S.chartedSpace
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : S.Point → Type _) :=
    ⟨S.metricOnPoints.toRiemannianMetric⟩
  let q := spacetimeSlicePoint G.slices (R.curve s)
  let D := G.leafwise.sliceConnection (G.spacetime.timeFunction (R.curve s))
  let j := S.tangentEquiv q
  let es := e.map j.symm.toLinearEquiv
  have hes : Orthonormal ℝ es := by
    apply orthonormal_iff_ite.mpr
    intro i k
    change S.metricOnPoints.inner q (es i) (es k) = _
    rw [S.metric_eq]
    simpa only [es, j, S, q, spacetimeSlicePoint, Module.Basis.map_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.apply_symm_apply] using he i k
  have hWs (i : Fin n) (v : TangentSpace (𝓡 n) q) :
      S.metricOnPoints.inner q (j.symm (W i)) v =
        fp * S.metricOnPoints.inner q (es i) v - 2 * s * f * D.ricci q (es i) v := by
    rw [S.metric_eq, S.metric_eq]
    simpa only [es, j, S, q, D, spacetimeSlicePoint, Module.Basis.map_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.apply_symm_apply, horizontalRicci,
      ContinuousLinearEquiv.symm_apply_apply] using hW i (j v)
  have ht := sliceIndexDensity_adapted_trace_of_pair hM04 D q s
    (j.symm (R.horizontal_velocity s)) f fp (es.toOrthonormalBasis hes)
    (fun i => j.symm (W i)) (by simpa only [Module.Basis.coe_toOrthonormalBasis] using hWs)
  simp_rw [horizontalIndexPairDensity_eq_slice R]
  dsimp only [Module.Basis.coe_toOrthonormalBasis, es, j, S, q, D, spacetimeSlicePoint,
    Module.Basis.map_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    horizontalScalarCurvature, horizontalRicci] at ht ⊢
  simp only [Module.Basis.coe_toOrthonormalBasis, Module.Basis.map_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv] at ht
  refine Eq.trans ?_ ht
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun v => sliceIndexDensity D q s (j.symm (R.horizontal_velocity s)) v
    (j.symm (W i))) (j.symm.map_smul f (e i))

end PoincareConjecture.M14
