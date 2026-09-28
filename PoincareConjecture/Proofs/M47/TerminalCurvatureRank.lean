import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Rank

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

open RicciFlow.Splitting

theorem terminalCurvature_ricci_nullity_eq_one
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b,
      ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hkernel : ∃ x z, z ≠ 0 ∧ ∀ w, (F.connection b).ricci x z w = 0)
    (hnonflat : ∃ p, (F.connection b).curvatureTensorNorm p ≠ 0)
    (hC : RicciFlowCurvatureTheory.{u}) :
    ∀ x, ricciNullity (F.connection b) x = 1 := by
  have hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature :=
    fun t ht x => (F.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t ht x)
  obtain ⟨x0, z, hz, hzr⟩ := hkernel
  obtain ⟨p, hp⟩ := hnonflat
  have hpos : 0 < ricciNullity (F.connection b) x0 := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨z, (mem_ricciKernel _ _ _).mpr hzr⟩,
      fun h => hz (congrArg Subtype.val h)⟩
  have hspace (y z : M) : ricciNullity (F.connection b) y =
      ricciNullity (F.connection b) z :=
    ricciNullity_eq_on_positive_slice hC hab F hsec
      (show b ∈ Ioc a b from ⟨hab, le_rfl⟩) y z
  have hupper := (F.connection b).ricciNullity_le_one_of_nonflat
    (hC.tensor_calculus 3 M (F.metric b) (F.connection b)) p
    (hoperator b (right_mem_Icc.mpr hab.le) p) hp
  intro x
  have hx0 := hspace x x0
  have hxp := hspace x p
  omega

end PoincareConjecture.M47
