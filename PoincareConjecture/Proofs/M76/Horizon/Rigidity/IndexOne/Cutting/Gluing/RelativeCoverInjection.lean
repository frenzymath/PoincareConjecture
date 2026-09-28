import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Gluing.ClosedCoverInjection

set_option autoImplicit false
open Set BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

private def relativeSetHomeomorph
    {X : Type*} [TopologicalSpace X] {R A : Set X} (hAR : A ⊆ R) :
    ((Subtype.val : R → X) ⁻¹' A) ≃ₜ A where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hAR x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem relative_closed_cover_sides_pi1_injective
    {X : Type*} [MetricSpace X] {R N M : Set X}
    (hN : IsCompact N) (hM : IsCompact M) (hNR : N ⊆ R) (hMR : M ⊆ R)
    (hcover : N ∪ M = R) (hne : (N ∩ M).Nonempty)
    (hlocalN : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) N,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_left a)
    (hlocalM : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) M,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_right a)
    (hpiN : ∀ x : ↥(N ∩ M), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) x))
    (hpiM : ∀ x : ↥(N ∩ M), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) x)) :
    (∀ x : N, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hNR) x)) ∧
    ∀ x : M, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hMR) x) := by
  let P : Set R := (Subtype.val : R → X) ⁻¹' N
  let Q : Set R := (Subtype.val : R → X) ⁻¹' M
  let HP : P ≃ₜ N := relativeSetHomeomorph hNR
  let HQ : Q ≃ₜ M := relativeSetHomeomorph hMR
  let HB : ↥(P ∩ Q) ≃ₜ ↥(N ∩ M) :=
    relativeSetHomeomorph (inter_subset_left.trans hNR)
  have hP : IsClosed P := hN.isClosed.preimage continuous_subtype_val
  have hQ : IsClosed Q := hM.isClosed.preimage continuous_subtype_val
  have hcover' : P ∪ Q = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    exact hcover.symm.subset x.property
  have hcompact : IsCompact (P ∩ Q) := by
    let : CompactSpace ↥(N ∩ M) := isCompact_iff_compactSpace.mp (hN.inter_right hM.isClosed)
    let : CompactSpace ↥(P ∩ Q) := HB.symm.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hne' : (P ∩ Q).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hNR hx.1⟩, hx⟩
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
  have hpiP : ∀ x : ↥(P ∩ Q), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) x) := by
    intro x a b hab
    apply (FundamentalGroup.map_bijective_of_homotopyEquiv HB.toHomotopyEquiv x).1
    change FundamentalGroup.map (⟨HB, HB.continuous⟩ : C(↥(P ∩ Q), ↥(N ∩ M))) x a =
      FundamentalGroup.map (⟨HB, HB.continuous⟩ : C(↥(P ∩ Q), ↥(N ∩ M))) x b
    apply hpiN (HB x)
    have h := congrArg
      (FundamentalGroup.map (⟨HP, HP.continuous⟩ : C(P, N))
        (ContinuousMap.inclusion inter_subset_left x)) hab
    rw [← FundamentalGroup.map_comp_apply, ← FundamentalGroup.map_comp_apply] at h
    have h' : FundamentalGroup.map ((ContinuousMap.inclusion inter_subset_left).comp
        (⟨HB, HB.continuous⟩ : C(↥(P ∩ Q), ↥(N ∩ M)))) x a =
      FundamentalGroup.map ((ContinuousMap.inclusion inter_subset_left).comp
        (⟨HB, HB.continuous⟩ : C(↥(P ∩ Q), ↥(N ∩ M)))) x b := h
    rw [FundamentalGroup.map_comp_apply, FundamentalGroup.map_comp_apply] at h'
    exact h'
  have hpiQ : ∀ x : ↥(P ∩ Q), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) x) := by
    intro x a b hab
    apply (FundamentalGroup.map_bijective_of_homotopyEquiv HB.toHomotopyEquiv x).1
    change FundamentalGroup.map (⟨HB, HB.continuous⟩ : C(↥(P ∩ Q), ↥(N ∩ M))) x a =
      FundamentalGroup.map (⟨HB, HB.continuous⟩ : C(↥(P ∩ Q), ↥(N ∩ M))) x b
    apply hpiM (HB x)
    have h := congrArg
      (FundamentalGroup.map (⟨HQ, HQ.continuous⟩ : C(Q, M))
        (ContinuousMap.inclusion inter_subset_right x)) hab
    rw [← FundamentalGroup.map_comp_apply, ← FundamentalGroup.map_comp_apply] at h
    have h' : FundamentalGroup.map ((ContinuousMap.inclusion inter_subset_right).comp
        (⟨HB, HB.continuous⟩ : C(↥(P ∩ Q), ↥(N ∩ M)))) x a =
      FundamentalGroup.map ((ContinuousMap.inclusion inter_subset_right).comp
        (⟨HB, HB.continuous⟩ : C(↥(P ∩ Q), ↥(N ∩ M)))) x b := h
    rw [FundamentalGroup.map_comp_apply, FundamentalGroup.map_comp_apply] at h'
    exact h'
  have hglue := closed_cover_sides_pi1_injective hP hQ hcover' hcompact hne'
    hlocalP hlocalQ hpiP hpiQ
  constructor
  · intro x a b hab
    apply (FundamentalGroup.map_bijective_of_homotopyEquiv HP.symm.toHomotopyEquiv x).1
    change FundamentalGroup.map (⟨HP.symm, HP.symm.continuous⟩ : C(N, P)) x a =
      FundamentalGroup.map (⟨HP.symm, HP.symm.continuous⟩ : C(N, P)) x b
    apply hglue P (Or.inl rfl) (HP.symm x)
    have h : FundamentalGroup.map ((VanKampen.inclusion P).comp
        (⟨HP.symm, HP.symm.continuous⟩ : C(N, P))) x a =
      FundamentalGroup.map ((VanKampen.inclusion P).comp
        (⟨HP.symm, HP.symm.continuous⟩ : C(N, P))) x b := hab
    rw [FundamentalGroup.map_comp_apply, FundamentalGroup.map_comp_apply] at h
    exact h
  · intro x a b hab
    apply (FundamentalGroup.map_bijective_of_homotopyEquiv HQ.symm.toHomotopyEquiv x).1
    change FundamentalGroup.map (⟨HQ.symm, HQ.symm.continuous⟩ : C(M, Q)) x a =
      FundamentalGroup.map (⟨HQ.symm, HQ.symm.continuous⟩ : C(M, Q)) x b
    apply hglue Q (Or.inr rfl) (HQ.symm x)
    have h : FundamentalGroup.map ((VanKampen.inclusion Q).comp
        (⟨HQ.symm, HQ.symm.continuous⟩ : C(M, Q))) x a =
      FundamentalGroup.map ((VanKampen.inclusion Q).comp
        (⟨HQ.symm, HQ.symm.continuous⟩ : C(M, Q))) x b := hab
    rw [FundamentalGroup.map_comp_apply, FundamentalGroup.map_comp_apply] at h
    exact h

end PoincareConjecture.M76.HamiltonIntervalTorus
