import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Restricting both sides of an open transition

The inclusion chart of an open subset conjugates an ambient partial
homeomorphism to a transition between copies of the subset. This is the
topological restriction used in the compact double of Morgan-Tian
Theorem 12.5, p. 297; see the compact-double derivation in the task records.
-/

set_option autoImplicit false

open Set Topology

universe u

namespace OpenPartialHomeomorph

variable {X : Type u} [TopologicalSpace X] (e : OpenPartialHomeomorph X X)
  {U : Set X} (hU : IsOpen U) [Nonempty U]

/-- Conjugation by an open inclusion restricts both sides of a transition
(Morgan-Tian Theorem 12.5, p. 297, compact-double derivation). -/
noncomputable def onOpenSubset : OpenPartialHomeomorph U U :=
  let j := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  (j.trans e).trans j.symm

/-- If the ambient target is retained, restriction introduces no further
source condition (Theorem 12.5, p. 297, compact-double derivation). -/
theorem onOpenSubset_source (htarget : e.target ⊆ U) :
    (e.onOpenSubset hU).source = (Subtype.val : U → X) ⁻¹' e.source := by
  ext x
  simp only [onOpenSubset, trans_source, mem_inter_iff, mem_preimage,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, mem_univ, true_and,
    trans_apply, IsOpenEmbedding.toOpenPartialHomeomorph_apply, symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_coe]
  exact and_iff_left_of_imp (fun hx => htarget (e.map_source hx))

/-- The restricted transition has the ambient value wherever that value
lies in the open subset (Theorem 12.5, p. 297, compact-double derivation). -/
theorem onOpenSubset_apply_coe (x : U) (hx : e (x : X) ∈ U) :
    ((e.onOpenSubset hU x : U) : X) = e (x : X) := by
  simp only [onOpenSubset, trans_apply, IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  exact IsOpenEmbedding.toOpenPartialHomeomorph_right_inv Subtype.val
    hU.isOpenEmbedding_subtypeVal (by simpa only [Subtype.range_coe] using hx)

/-- Inversion commutes with restriction to both open subsets
(Theorem 12.5, p. 297, compact-double derivation). -/
theorem onOpenSubset_symm : (e.onOpenSubset hU).symm = e.symm.onOpenSubset hU := by
  simp only [onOpenSubset, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]

/-- A self-inverse ambient transition remains self-inverse after restriction
(Theorem 12.5, p. 297, compact-double derivation). -/
theorem onOpenSubset_symm_eq (he : e.symm = e) :
    (e.onOpenSubset hU).symm = e.onOpenSubset hU := by
  rw [onOpenSubset_symm, he]

end OpenPartialHomeomorph
