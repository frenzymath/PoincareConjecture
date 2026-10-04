import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact sets through an open partial inverse

Morgan--Tian Claim 11.35, printed p. 290. The compact cap core is moved
through the actual partial inverse before the global product chart is used.
Reviewed derivation: `claim11_35-fixed-time-cap-exclusion.md`, section 2.
-/

set_option autoImplicit false

open Set

universe u v

namespace PoincareMT.M32

/-- Compactness and ambient interior/frontier are preserved by an open
partial inverse on a compact subset of its target. This is the compact-core
transport used in Claim 11.35, printed p. 290. -/
theorem compact_partial_inverse_geometry
    {M : Type u} {L : Type v} [TopologicalSpace M] [TopologicalSpace L]
    [T2Space M] [T2Space L] (E : OpenPartialHomeomorph L M)
    {K : Set M} (hK : IsCompact K) (htarget : K ⊆ E.target) :
    IsCompact (E.symm '' K) ∧ E.symm '' K ⊆ E.source ∧
      interior (E.symm '' K) = E.symm '' interior K ∧
      frontier (E.symm '' K) = E.symm '' frontier K := by
  have hcompact : IsCompact (E.symm '' K) :=
    hK.image_of_continuousOn (E.symm.continuousOn.mono htarget)
  have hsource : E.symm '' K ⊆ E.source := by
    rintro x ⟨y, hy, rfl⟩
    exact E.map_target (htarget hy)
  have himage : E.IsImage (E.symm '' K) K := by
    intro x hx
    constructor
    · intro h
      exact ⟨E x, h, E.left_inv hx⟩
    · rintro ⟨y, hy, rfl⟩
      rwa [E.right_inv (htarget hy)]
  refine ⟨hcompact, hsource, ?_, ?_⟩
  · have h := himage.interior.symm_image_eq
    rw [inter_eq_right.mpr (interior_subset.trans htarget),
      inter_eq_right.mpr (interior_subset.trans hsource)] at h
    exact h.symm
  · have h := himage.frontier.symm_image_eq
    rw [inter_eq_right.mpr (hK.isClosed.frontier_subset.trans htarget),
      inter_eq_right.mpr (hcompact.isClosed.frontier_subset.trans hsource)] at h
    exact h.symm

end PoincareMT.M32
