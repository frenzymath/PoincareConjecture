import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.Capping.ClosedCover



set_option autoImplicit false
open Set BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

private def cappingRelativeSetHomeomorph
    {X : Type*} [TopologicalSpace X] {R A : Set X} (hAR : A ⊆ R) :
    ((Subtype.val : R → X) ⁻¹' A) ≃ₜ A where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hAR x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _




theorem isSimplyConnected_union_of_closed_cover_capping
    {X : Type*} [MetricSpace X] {N M : Set X}
    (hN : IsClosed N) (hM : IsClosed M) (hcompact : IsCompact (N ∩ M))
    (hNp : IsPathConnected N) (hMs : IsSimplyConnected M)
    (hWp : IsPathConnected (N ∩ M)) (b : ↥(N ∩ M))
    (hgenerate : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (inter_subset_left : N ∩ M ⊆ N)) b))
    (hlocalN : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) N,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_left a)
    (hlocalM : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) M,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_right a) :
    IsSimplyConnected (N ∪ M) := by
  let R := N ∪ M
  let P : Set R := (Subtype.val : R → X) ⁻¹' N
  let Q : Set R := (Subtype.val : R → X) ⁻¹' M
  let HP : P ≃ₜ N := cappingRelativeSetHomeomorph subset_union_left
  let HQ : Q ≃ₜ M := cappingRelativeSetHomeomorph subset_union_right
  let HB : ↥(P ∩ Q) ≃ₜ ↥(N ∩ M) :=
    cappingRelativeSetHomeomorph (inter_subset_left.trans subset_union_left)
  have hP : IsClosed P := hN.preimage continuous_subtype_val
  have hQ : IsClosed Q := hM.preimage continuous_subtype_val
  have hcover : P ∪ Q = univ := by
    ext x
    exact iff_true_intro x.property
  have hcompact' : IsCompact (P ∩ Q) := by
    let : CompactSpace ↥(N ∩ M) := isCompact_iff_compactSpace.mp hcompact
    let : CompactSpace ↥(P ∩ Q) := HB.symm.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hPp : IsPathConnected P := by
    let : PathConnectedSpace N := isPathConnected_iff_pathConnectedSpace.mp hNp
    exact isPathConnected_iff_pathConnectedSpace.mpr
      (pathConnectedSpace_of_homotopyEquiv HP.symm.toHomotopyEquiv)
  have hQs : IsSimplyConnected Q := by
    let : SimplyConnectedSpace M := hMs
    exact HQ.toHomotopyEquiv.simplyConnectedSpace
  have hW' : IsPathConnected (P ∩ Q) := by
    let : PathConnectedSpace ↥(N ∩ M) := isPathConnected_iff_pathConnectedSpace.mp hWp
    exact isPathConnected_iff_pathConnectedSpace.mpr
      (pathConnectedSpace_of_homotopyEquiv HB.symm.toHomotopyEquiv)
  have hlocalP : ∀ x : ↥(P ∩ Q),
      ∃ c : OpenPartialHomeomorph (↥(P ∩ Q) × Ico (0 : ℝ) 1) P,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_left a := by
    intro x
    obtain ⟨c, hx, hc⟩ := hlocalN (HB x)
    let D := HB.prodCongr (Homeomorph.refl (Ico (0 : ℝ) 1))
    refine ⟨(D.transOpenPartialHomeomorph c).transHomeomorph HP.symm, hx, ?_⟩
    intro a ha
    change HP.symm (c (collarBase (HB a))) = Set.inclusion inter_subset_left a
    rw [hc (HB a) ha]
    rfl
  have hlocalQ : ∀ x : ↥(P ∩ Q),
      ∃ c : OpenPartialHomeomorph (↥(P ∩ Q) × Ico (0 : ℝ) 1) Q,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_right a := by
    intro x
    obtain ⟨c, hx, hc⟩ := hlocalM (HB x)
    let D := HB.prodCongr (Homeomorph.refl (Ico (0 : ℝ) 1))
    refine ⟨(D.transOpenPartialHomeomorph c).transHomeomorph HQ.symm, hx, ?_⟩
    intro a ha
    change HQ.symm (c (collarBase (HB a))) = Set.inclusion inter_subset_right a
    rw [hc (HB a) ha]
    rfl
  let b' : ↥(P ∩ Q) := HB.symm b
  have hgenerate' : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (inter_subset_left : P ∩ Q ⊆ P)) b') := by
    let bP : P := ContinuousMap.inclusion (inter_subset_left : P ∩ Q ⊆ P) b'
    intro a
    obtain ⟨z, hz⟩ := hgenerate (FundamentalGroup.map (⟨HP, HP.continuous⟩ : C(P, N)) bP a)
    obtain ⟨d, hd⟩ := (FundamentalGroup.map_bijective_of_homotopyEquiv HB.toHomotopyEquiv b').2 z
    refine ⟨d, ?_⟩
    apply (FundamentalGroup.map_bijective_of_homotopyEquiv HP.toHomotopyEquiv bP).1
    change FundamentalGroup.map (⟨HP, HP.continuous⟩ : C(P, N))
      (ContinuousMap.inclusion (inter_subset_left : P ∩ Q ⊆ P) b')
      (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : P ∩ Q ⊆ P)) b' d) = _
    rw [← FundamentalGroup.map_comp_apply]
    change FundamentalGroup.map ((ContinuousMap.inclusion (inter_subset_left : N ∩ M ⊆ N)).comp
      (⟨HB, HB.continuous⟩ : C(↥(P ∩ Q), ↥(N ∩ M)))) b' d = _
    rw [FundamentalGroup.map_comp_apply]
    exact (congrArg (FundamentalGroup.map
      (ContinuousMap.inclusion (inter_subset_left : N ∩ M ⊆ N)) b) hd).trans hz
  exact simplyConnectedSpace_of_closed_cover_capping hP hQ hcover hcompact'
    hPp hQs hW' b' hgenerate' hlocalP hlocalQ

end PoincareConjecture.M76.HamiltonIntervalTorus
