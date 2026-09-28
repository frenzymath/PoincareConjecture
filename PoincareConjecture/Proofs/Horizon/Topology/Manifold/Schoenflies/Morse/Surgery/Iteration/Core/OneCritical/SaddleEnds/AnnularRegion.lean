import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.ComponentBand

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

variable {M : Type*} [TopologicalSpace M] [T2Space M]

theorem isClopen_annular_strip_in_region
    (F : OpenPartialHomeomorph (S1 × Real) M) {l a b u : Real}
    (hla : l < a) (hbu : b < u)
    (hsource : F.source = univ ×ˢ Ioo l u)
    {h : M → Real} (hheight : ∀ q t, t ∈ Ioo l u → h (F (q, t)) = t)
    {C : Set M} (hwindow : ∀ p ∈ C ∩ F.target, h p ∈ Icc a b) :
    IsClopen ((Subtype.val : C → M) ⁻¹' (F '' (univ ×ˢ Icc a b))) := by
  have hstrip : univ ×ˢ Icc a b ⊆ F.source := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact hsource ▸ ⟨hq, ⟨hla.trans_le ht.1, ht.2.trans_lt hbu⟩⟩
  have hcompact : IsCompact (F '' (univ ×ˢ Icc a b)) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn (F.continuousOn.mono hstrip)
  have heq : (Subtype.val : C → M) ⁻¹' (F '' (univ ×ˢ Icc a b)) =
      Subtype.val ⁻¹' F.target := by
    ext p
    constructor
    · rintro ⟨z, hz, hzp⟩
      change (p : M) ∈ F.target
      exact hzp ▸ F.map_source (hstrip hz)
    · intro hp
      have hz := F.map_target hp
      have hh := hheight (F.symm p).1 (F.symm p).2 (hsource ▸ hz).2
      rw [F.right_inv hp] at hh
      refine ⟨F.symm p, ⟨mem_univ _, ?_⟩, F.right_inv hp⟩
      rw [← hh]
      exact hwindow p ⟨p.property, hp⟩
  refine ⟨hcompact.isClosed.preimage continuous_subtype_val, ?_⟩
  rw [heq]
  exact F.open_target.preimage continuous_subtype_val

theorem subset_annular_strip_of_isPreconnected
    (F : OpenPartialHomeomorph (S1 × Real) M) {l a b u : Real}
    (hla : l < a) (hbu : b < u)
    (hsource : F.source = univ ×ˢ Ioo l u)
    {h : M → Real} (hheight : ∀ q t, t ∈ Ioo l u → h (F (q, t)) = t)
    {C : Set M} (hC : IsPreconnected C)
    (hwindow : ∀ p ∈ C ∩ F.target, h p ∈ Icc a b)
    (hmeet : (C ∩ F '' (univ ×ˢ Icc a b)).Nonempty) :
    C ⊆ F '' (univ ×ˢ Icc a b) := by
  have hclopen := isClopen_annular_strip_in_region F hla hbu hsource hheight hwindow
  obtain ⟨p, hpC, hpF⟩ := hmeet
  have hcomponent := hC.subset_connectedComponentIn hpC (Subset.rfl : C ⊆ C)
  intro y hy
  have hycomp := hcomponent hy
  rw [connectedComponentIn_eq_image hpC] at hycomp
  obtain ⟨q, hq, rfl⟩ := hycomp
  exact hclopen.connectedComponent_subset hpF hq

end Poincare.Manifold.Schoenflies
