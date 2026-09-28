import PoincareConjecture.Proofs.M47.TerminalCurvatureAmbientRank
import PoincareConjecture.Proofs.M47.TerminalCurvatureAmbientParallel
import PoincareConjecture.Proofs.M47.TerminalCurvatureOrientationCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

open RicciFlow.Splitting

theorem terminalCurvature_exhaustion_triple
    {M : Type*} [TopologicalSpace M] (U : ℕ → Opens M)
    (hmono : Monotone fun i => (U i : Set M))
    (hcover : (⋃ i, (U i : Set M)) = univ) (p x y : M) :
    ∃ i, p ∈ U i ∧ x ∈ U i ∧ y ∈ U i := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ p)
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ y)
  exact ⟨max i (max j k), hmono (le_max_left _ _) hi,
    hmono ((le_max_left _ _).trans (le_max_right _ _)) hj,
    hmono ((le_max_right _ _).trans (le_max_right _ _)) hk⟩

theorem terminalCurvature_null_line_of_finite_germs
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
    (∀ y, ricciNullity D y = 1) ∧
      (∀ y : M, ∃ (O : Set M) (V : (z : M) → TangentSpace (𝓡 3) z),
        IsOpen O ∧ y ∈ O ∧
        ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) O ∧
        ∀ z ∈ O, g.inner z (V z) (V z) = 1 ∧
          (∀ u, D.ricci z (V z) u = 0) ∧ ∀ u, D.connection V z u = 0) ∧
      Nonempty (NullOrientationCover D) := by
  have hrank := terminalCurvature_ambient_rank_one D hC U tau htau F hmetric hoperator
    p hscalar x v w hv hw hvw hzero hcover
  have hsec : ∀ i t, t ∈ Icc (-tau i) 0 →
      ((F i).connection t).NonnegativeSectionalCurvature :=
    fun i t ht y =>
      ((F i).connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        y (hoperator i t ht y)
  have hsingle (y : M) : ∃ i, y ∈ U i := by
    obtain ⟨i, _, _, hy⟩ := hcover y
    exact ⟨i, hy⟩
  have hlocal := terminalCurvature_ambient_local_parallel D hC hrank U tau htau F
    hmetric hsec hsingle
  refine ⟨hrank, hlocal, terminalCurvature_orientation_cover D hrank ?_⟩
  intro y
  obtain ⟨O, V, hO, hy, hV, hn⟩ := hlocal y
  exact ⟨O, V, hO, hy, hV, fun z hz => ⟨(hn z hz).1, (hn z hz).2.1⟩⟩

end PoincareConjecture.M47
