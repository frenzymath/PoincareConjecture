import PoincareConjecture.Proofs.M47.TerminalCurvatureOpenInclusion
import PoincareConjecture.Proofs.M47.TerminalCurvatureLocalParallel











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

open RicciFlow.Splitting



theorem terminalCurvature_ambient_rank_one
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hC : RicciFlowCurvatureTheory.{u})
    {ι : Type*} (U : ι → Opens M) [∀ i, ConnectedSpace (U i)]
    (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow 3 (U i) (Icc (-tau i) 0))
    (hmetric : ∀ i (y : U i) (v w : TangentSpace (𝓡 3) y),
      ((F i).metric 0).inner y v w = g.inner y.val v w)
    (hoperator : ∀ i t, t ∈ Icc (-tau i) 0 → ∀ y,
      ((F i).connection t).NonnegativeCurvatureOperator y)
    (p : M) (hscalar : D.scalarCurvature p ≠ 0)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1)
    (hvw : g.inner x v w = 0) (hzero : D.curvatureTensor x v w v w = 0)
    (hcover : ∀ y : M, ∃ i, p ∈ U i ∧ x ∈ U i ∧ y ∈ U i) :
    ∀ y, ricciNullity D y = 1 := by
  intro y
  obtain ⟨i, hp, hx, hy⟩ := hcover y
  let pi : U i := ⟨p, hp⟩
  let xi : U i := ⟨x, hx⟩
  let yi : U i := ⟨y, hy⟩
  have hread := terminalCurvature_open_inclusion_readouts D (U i)
    ((F i).connection 0) (hmetric i)
  have hpi : ((F i).connection 0).scalarCurvature pi ≠ 0 := by
    rw [(hread pi).1]
    exact hscalar
  have hxi : ((F i).connection 0).curvatureTensor xi v w v w = 0 := by
    rw [(hread xi).2.1]
    exact hzero
  have hrank := terminalCurvature_rank_one_of_null_plane hC
    (show -tau i < 0 by linarith [htau i]) (F i) (hoperator i)
    pi hpi xi v w ((hmetric i xi v v).trans hv)
    ((hmetric i xi w w).trans hw) ((hmetric i xi v w).trans hvw) hxi yi
  exact (hread yi).2.2.2.2.symm.trans hrank

end PoincareConjecture.M47
