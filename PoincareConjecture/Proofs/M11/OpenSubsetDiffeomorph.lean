import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem openSubset_localDiffeomorph (U : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph J J ∞ (Subtype.val : U → M) := by
  intro x
  let e := U.openPartialHomeomorphSubtypeCoe ⟨x⟩
  have hi : ContMDiffOn J J ∞ e.symm e.target := by
    intro p hp
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target p).mp
    apply contMDiffWithinAt_id.congr_of_mem _ hp
    intro q hq
    exact e.right_inv hq
  exact ⟨{
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := hi
  }, mem_univ x, fun _ _ ↦ rfl⟩

theorem openSubset_differential_injective (U : TopologicalSpace.Opens M) (x : U) :
    Function.Injective (mfderiv J J (Subtype.val : U → M) x) :=
  ((openSubset_localDiffeomorph (J := J) U x).mfderivToContinuousLinearEquiv (by simp)).injective

end PoincareConjecture.Proofs.M11
