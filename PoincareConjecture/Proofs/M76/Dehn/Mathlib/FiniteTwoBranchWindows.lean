import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CompactDoubleRelation
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoBranchWindows










set_option autoImplicit false

open Set Topology






theorem IsLocalHomeomorph.exists_finite_twoBranchWindows
    {D X Y : Type*} [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace D] [T2Space X] [T2Space Y]
    {r : X → Y} (hr : IsLocalHomeomorph r)
    (hf : ∀ y, (r ⁻¹' {y}).Finite) (hn : ∀ y, (r ⁻¹' {y}).ncard ≤ 2)
    {j : D → X} (hj : IsEmbedding j) :
    ∃ W : Finset (TwoBranchWindow r), ∀ x y : D,
      r (j x) = r (j y) → x ≠ y →
      ∃ w ∈ W, j x ∈ w.left.source ∧ j y ∈ w.right.source := by
  classical
  let B : Set (D × D) := {z | r (j z.1) = r (j z.2) ∧ z.1 ≠ z.2}
  have hlocal : IsLocallyInjective (r ∘ j) :=
    hr.isLocallyInjective.comp_right hj.continuous hj.injective
  have hcompact : IsCompact B :=
    hlocal.isCompact_doubleRelation (hr.continuous.comp hj.continuous)
  have hwindow : ∀ z : B, ∃ w : TwoBranchWindow r,
      j z.val.1 ∈ w.left.source ∧ j z.val.2 ∈ w.right.source := by
    intro z
    exact hr.exists_twoBranchWindow hf hn z.property.1
      (fun h => z.property.2 (hj.injective h))
  choose w hw using hwindow
  let V : B → Set (D × D) := fun z =>
    (j ⁻¹' (w z).left.source) ×ˢ (j ⁻¹' (w z).right.source)
  have hV : ∀ z, IsOpen (V z) := fun z =>
    ((w z).left.open_source.preimage hj.continuous).prod
      ((w z).right.open_source.preimage hj.continuous)
  have hcover : B ⊆ ⋃ z, V z := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hw ⟨z, hz⟩⟩
  obtain ⟨T, hT⟩ := hcompact.elim_finite_subcover V hV hcover
  refine ⟨T.image w, ?_⟩
  intro x y he hne
  obtain ⟨z, hz⟩ := mem_iUnion.mp (hT (show (x, y) ∈ B from ⟨he, hne⟩))
  obtain ⟨hzT, hxy⟩ := mem_iUnion.mp hz
  exact ⟨w z, Finset.mem_image.mpr ⟨z, hzT, rfl⟩, hxy⟩
