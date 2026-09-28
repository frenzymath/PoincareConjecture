import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import PoincareConjecture.Definitions.Ch01.RiemannianMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]

noncomputable def smoothPartialSubtype
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) U N ∞ where
  toPartialEquiv := (e.toOpenPartialHomeomorph.subtypeRestr hU).toPartialEquiv
  open_source := (e.toOpenPartialHomeomorph.subtypeRestr hU).open_source
  open_target := (e.toOpenPartialHomeomorph.subtypeRestr hU).open_target
  contMDiffOn_toFun := by
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e ∘ Subtype.val) _
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact e.contMDiffOn_toFun.comp contMDiff_subtype_val.contMDiffOn (fun _ hx => hx)
  contMDiffOn_invFun := by
    let r := e.toOpenPartialHomeomorph.subtypeRestr hU
    have h : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ r.symm) r.target :=
      (e.contMDiffOn_invFun.mono
        (e.toOpenPartialHomeomorph.subtypeRestr_target_subset hU)).congr
          (fun _ hy => e.toOpenPartialHomeomorph.subtypeRestr_symm_apply hU hy)
    intro y hy
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U r.symm r.target y).mp (h y hy)

theorem partialSubtype_target (e : OpenPartialHomeomorph M N)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (hsource : e.source ⊆ U) : (e.subtypeRestr hU).target = e.target := by
  apply Set.Subset.antisymm (e.subtypeRestr_target_subset hU)
  intro y hy
  refine ⟨hy, ?_⟩
  simpa only [Set.mem_preimage, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    using hsource (e.map_target hy)

theorem partialSubtype_both_source (e : OpenPartialHomeomorph M N)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (V : TopologicalSpace.Opens N) (hV : Nonempty V)
    (htarget : e.target ⊆ V) :
    ((e.subtypeRestr hU).symm.subtypeRestr hV).symm.source =
      Subtype.val ⁻¹' e.source := by
  rw [OpenPartialHomeomorph.symm_source, partialSubtype_target _ V hV
    ((e.subtypeRestr_target_subset hU).trans htarget), OpenPartialHomeomorph.symm_target]
  exact e.subtypeRestr_source hU

end PoincareConjecture.M38
