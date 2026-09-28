import PoincareConjecture.Proofs.M47.TerminalCurvatureNullPlane
import PoincareConjecture.Proofs.M47.TerminalCurvatureRank
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.LocalParallel











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

open RicciFlow.Splitting



theorem terminalCurvature_rank_one_of_null_plane
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (p : M) (hscalar : (F.connection b).scalarCurvature p ≠ 0)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric b).inner x v v = 1)
    (hw : (F.metric b).inner x w w = 1)
    (hvw : (F.metric b).inner x v w = 0)
    (hzero : (F.connection b).curvatureTensor x v w v w = 0) :
    ∀ y, ricciNullity (F.connection b) y = 1 := by
  have hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature :=
    fun t ht y => (F.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      y (hoperator t ht y)
  obtain ⟨z, hz, hzr⟩ :=
    terminalCurvature_exists_ricci_null_vector hC hab F hsec x v w hv hw hvw hzero
  have hnonflat : (F.connection b).curvatureTensorNorm p ≠ 0 := by
    intro hflat
    have hbound := (F.connection b).abs_scalarCurvature_le_curvatureTensorNorm_sharp p
    rw [hflat, mul_zero] at hbound
    exact hscalar (abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _)))
  exact terminalCurvature_ricci_nullity_eq_one hab F hoperator
    ⟨x, z, hz, hzr⟩ ⟨p, hnonflat⟩ hC



theorem terminalCurvature_local_parallel_of_null_plane
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (p : M) (hscalar : (F.connection b).scalarCurvature p ≠ 0)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric b).inner x v v = 1)
    (hw : (F.metric b).inner x w w = 1)
    (hvw : (F.metric b).inner x v w = 0)
    (hzero : (F.connection b).curvatureTensor x v w v w = 0)
    (y : M) :
    ricciNullity (F.connection b) y = 1 ∧
      ∃ (U : Set M) (V : (z : M) → TangentSpace (𝓡 3) z),
        IsOpen U ∧ y ∈ U ∧
        ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) U ∧
        ∀ z ∈ U, (F.metric b).inner z (V z) (V z) = 1 ∧
          (∀ u, (F.connection b).ricci z (V z) u = 0) ∧
          ∀ u, (F.connection b).connection V z u = 0 := by
  have hrank := terminalCurvature_rank_one_of_null_plane hC hab F hoperator
    p hscalar x v w hv hw hvw hzero
  have hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature :=
    fun t ht z => (F.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      z (hoperator t ht z)
  exact ⟨hrank y, exists_local_parallel_unit_ricci_null_section hC hab F hsec hrank y⟩

end PoincareConjecture.M47
