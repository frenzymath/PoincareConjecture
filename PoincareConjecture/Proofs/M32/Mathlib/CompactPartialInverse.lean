import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff









set_option autoImplicit false

open Set

universe u v

namespace PoincareConjecture.M32




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

end PoincareConjecture.M32
