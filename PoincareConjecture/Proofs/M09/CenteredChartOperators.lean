import PoincareConjecture.Proofs.M09.FrozenFrame
import PoincareConjecture.Proofs.M09.ChartVectorField
import PoincareConjecture.Definitions.Ch01.ScalarOperators
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem frozenExtend_eq_chartVectorField (p : M) (v : TangentSpace (𝓡 n) p)
    (q : M) (hq : q ∈ (chartAt E p).source) :
    FiberBundle.extend E v q = chartVectorField p v q := by
  have hbase : q ∈ (trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p).baseSet := hq
  rw [← extensionMap_apply p q hbase v]
  dsimp only [extensionMap]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓡 n)
      (mem_chart_source E p),
    mfderiv_extChartAt_self, ContinuousLinearMap.comp_id,
    TangentBundle.symmL_trivializationAt hq]
  have he : (extChartAt (𝓡 n) p) = (chartAt E p).toPartialEquiv := by
    ext x <;> simp
  rw [he]
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ]
  have h := chartVectorField_at_inverse p v ((chartAt E p) q) ((chartAt E p).map_source hq)
  convert! h.symm using 1
  rw [(chartAt E p).left_inv hq]

set_option backward.isDefEq.respectTransparency false in
theorem frozenExtend_eventuallyEq_chartVectorField (p : M) (v : TangentSpace (𝓡 n) p) :
    FiberBundle.extend («E» := TangentSpace (𝓡 n)) (x := p) E v =ᶠ[𝓝 p]
      chartVectorField p v := by
  filter_upwards [(chartAt E p).open_source.mem_nhds (mem_chart_source E p)] with q hq
  exact frozenExtend_eq_chartVectorField p v q hq

theorem chartVectorField_self (p : M) (v : TangentSpace (𝓡 n) p) :
    chartVectorField p v p = v := by
  rw [← frozenExtend_eq_chartVectorField p v p (mem_chart_source E p),
    FiberBundle.extend_apply_self]

theorem connection_frozenExtend_eq_chartVectorField {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) (X v : TangentSpace (𝓡 n) p) :
    D.connection (FiberBundle.extend E v) p X = D.connection (chartVectorField p v) p X := by
  have hv := ((chartVectorField_smooth p v).contMDiffAt
    ((chartAt E p).open_source.mem_nhds (mem_chart_source E p))).mdifferentiableAt (by simp)
  exact congrArg (fun L ↦ L X)
    (D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (FiberBundle.mdifferentiableAt_extend (𝓡 n) E v) hv (by simp)
      (frozenExtend_eventuallyEq_chartVectorField p v))

theorem covariantTensorDerivative_centeredChart {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (p : M) (X : TangentSpace (𝓡 n) p) (v : Fin k → TangentSpace (𝓡 n) p) :
    D.covariantTensorDerivative T p (Fin.cons X v) =
      mvfderiv (𝓡 n) (fun q ↦ T q (fun i ↦ chartVectorField p (v i) q)) p X -
        ∑ i, T p (Function.update v i (D.connection (chartVectorField p (v i)) p X)) := by
  classical
  have heq : (fun q ↦ T q (fun i ↦ FiberBundle.extend E (v i) q)) =ᶠ[𝓝 p]
      (fun q ↦ T q (fun i ↦ chartVectorField p (v i) q)) := by
    filter_upwards [(chartAt E p).open_source.mem_nhds (mem_chart_source E p)] with q hq
    simp only [frozenExtend_eq_chartVectorField p _ q hq]
  change mvfderiv (𝓡 n) (fun q ↦ T q (fun i ↦ FiberBundle.extend E (v i) q)) p X -
      ∑ i, T p (Function.update v i (D.connection (FiberBundle.extend E (v i)) p X)) = _
  simp only [connection_frozenExtend_eq_chartVectorField]
  rw [mvfderiv, mvfderiv, heq.mfderiv_eq]
  rfl

theorem hessian_centeredChart {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : M → ℝ) (p : M) (U V : TangentSpace (𝓡 n) p) :
    D.hessian f p U V = D.hessianOnFields f (chartVectorField p U) (chartVectorField p V) p := by
  have heq : (fun q ↦ mvfderiv (𝓡 n) f q (FiberBundle.extend E V q)) =ᶠ[𝓝 p]
      (fun q ↦ mvfderiv (𝓡 n) f q (chartVectorField p V q)) := by
    filter_upwards [frozenExtend_eventuallyEq_chartVectorField p V] with q hq
    rw [hq]
  have hd : mvfderiv (𝓡 n) (fun q ↦ mvfderiv (𝓡 n) f q (FiberBundle.extend E V q)) p =
      mvfderiv (𝓡 n) (fun q ↦ mvfderiv (𝓡 n) f q (chartVectorField p V q)) p := by
    rw [mvfderiv, mvfderiv, heq.mfderiv_eq]
    rfl
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self, chartVectorField_self,
    connection_frozenExtend_eq_chartVectorField, hd]

end PoincareConjecture.Proofs.M09
