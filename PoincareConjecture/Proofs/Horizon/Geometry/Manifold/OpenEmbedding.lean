import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare

theorem isLocalDiffeomorph_opensSubtypeVal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (U : Opens M) : IsLocalDiffeomorph I I ∞ (Subtype.val : U → M) := by
  intro x
  let : Nonempty U := ⟨x⟩
  let e := U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  let d : PartialDiffeomorph I I U M ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target y).mp
        apply contMDiffWithinAt_id.congr
        · intro z hz
          exact e.right_inv hz
        · exact e.right_inv hy }
  exact ⟨d, mem_univ x, fun _ _ => rfl⟩

end Poincare
