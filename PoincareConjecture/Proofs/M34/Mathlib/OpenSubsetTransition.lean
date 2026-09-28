import Mathlib.Topology.OpenPartialHomeomorph.Composition










set_option autoImplicit false

open Set Topology

universe u

namespace OpenPartialHomeomorph

variable {X : Type u} [TopologicalSpace X] (e : OpenPartialHomeomorph X X)
  {U : Set X} (hU : IsOpen U) [Nonempty U]



noncomputable def onOpenSubset : OpenPartialHomeomorph U U :=
  let j := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  (j.trans e).trans j.symm



theorem onOpenSubset_source (htarget : e.target ⊆ U) :
    (e.onOpenSubset hU).source = (Subtype.val : U → X) ⁻¹' e.source := by
  ext x
  simp only [onOpenSubset, trans_source, mem_inter_iff, mem_preimage,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, mem_univ, true_and,
    trans_apply, IsOpenEmbedding.toOpenPartialHomeomorph_apply, symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_coe]
  exact and_iff_left_of_imp (fun hx => htarget (e.map_source hx))



theorem onOpenSubset_apply_coe (x : U) (hx : e (x : X) ∈ U) :
    ((e.onOpenSubset hU x : U) : X) = e (x : X) := by
  simp only [onOpenSubset, trans_apply, IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  exact IsOpenEmbedding.toOpenPartialHomeomorph_right_inv Subtype.val
    hU.isOpenEmbedding_subtypeVal (by simpa only [Subtype.range_coe] using hx)



theorem onOpenSubset_symm : (e.onOpenSubset hU).symm = e.symm.onOpenSubset hU := by
  simp only [onOpenSubset, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]



theorem onOpenSubset_symm_eq (he : e.symm = e) :
    (e.onOpenSubset hU).symm = e.onOpenSubset hU := by
  rw [onOpenSubset_symm, he]

end OpenPartialHomeomorph
