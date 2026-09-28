import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.LevelComponents



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private theorem component_equiv_of_two_open_pieces
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) (hcover : U ∪ V = univ) :
    IsClopen U ∧ IsClopen V ∧
      (∀ x, Xor (connectedComponent x ⊆ U) (connectedComponent x ⊆ V)) ∧
      ∃ E : ConnectedComponents X ≃ ConnectedComponents U ⊕ ConnectedComponents V,
        (∀ x : U, E (ConnectedComponents.mk x.val) =
          Sum.inl (ConnectedComponents.mk x)) ∧
        ∀ x : V, E (ConnectedComponents.mk x.val) =
          Sum.inr (ConnectedComponents.mk x) := by
  have hcompl : Uᶜ = V := by
    ext x
    constructor
    · intro hx
      rcases hcover.symm ▸ mem_univ x with hu | hv
      · exact (hx hu).elim
      · exact hv
    · intro hx hu
      exact disjoint_left.mp hUV hu hx
  have hUc : IsClopen U := ⟨by rwa [← isOpen_compl_iff, hcompl], hU⟩
  have hVc : IsClopen V := ⟨by rw [← hcompl]; exact hU.isClosed_compl, hV⟩
  let W : Bool → Set X
    | false => U
    | true => V
  have hWclopen (i : Bool) : IsClopen (W i) := by cases i <;> assumption
  have hWdisj : Pairwise (Disjoint on W) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hUV
    · exact hUV.symm
    · exact (hij rfl).elim
  have hWcover : ⋃ i, W i = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    rcases hcover.symm ▸ mem_univ x with hu | hv
    · exact ⟨false, hu⟩
    · exact ⟨true, hv⟩
  let Q : (Σ i, ConnectedComponents (W i)) ≃
      ConnectedComponents U ⊕ ConnectedComponents V := {
    toFun := fun z => match z with
      | ⟨false, y⟩ => Sum.inl y
      | ⟨true, y⟩ => Sum.inr y
    invFun := fun z => match z with
      | Sum.inl y => ⟨false, y⟩
      | Sum.inr y => ⟨true, y⟩
    left_inv := by rintro ⟨(_ | _), y⟩ <;> rfl
    right_inv := by rintro (y | y) <;> rfl }
  let E := (ConnectedComponents.equivOfIsClopen hWclopen hWdisj hWcover).trans Q
  refine ⟨hUc, hVc, ?_, E, ?_, ?_⟩
  · intro x
    have hnot (hu : connectedComponent x ⊆ U) (hv : connectedComponent x ⊆ V) : False :=
      disjoint_left.mp hUV (hu mem_connectedComponent) (hv mem_connectedComponent)
    rcases hcover.symm ▸ mem_univ x with hu | hv
    · exact Or.inl ⟨hUc.connectedComponent_subset hu,
        fun hv => hnot (hUc.connectedComponent_subset hu) hv⟩
    · exact Or.inr ⟨hVc.connectedComponent_subset hv,
        fun hu => hnot hu (hVc.connectedComponent_subset hv)⟩
  · intro x
    change Q (ConnectedComponents.equivOfIsClopen hWclopen hWdisj hWcover
      (ConnectedComponents.mk x.val)) = _
    rw [ConnectedComponents.equivOfIsClopen_mk (i := false) hWclopen hWdisj hWcover x.val
      (show x.val ∈ W false from x.property)]
    rfl
  · intro x
    change Q (ConnectedComponents.equivOfIsClopen hWclopen hWdisj hWcover
      (ConnectedComponents.mk x.val)) = _
    rw [ConnectedComponents.equivOfIsClopen_mk (i := true) hWclopen hWdisj hWcover x.val
      (show x.val ∈ W true from x.property)]
    rfl




theorem other_level_components_of_parallel_disks
    {h : S2 → Real} {c ε a k : Real} (haε : a < ε) (hk : a < |k - c|)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hheight : ∀ q t, t ∈ Ioo (-ε) ε → h (T (q, t)) = c + t)
    (eMinus ePlus : OpenPartialHomeomorph E2 S2)
    (hsMinus : closedBall 0 1 ⊆ eMinus.source) (hsPlus : closedBall 0 1 ⊆ ePlus.source)
    (hdisjoint : Disjoint (eMinus '' closedBall 0 1) (ePlus '' closedBall 0 1))
    (hslab : T '' (univ ×ˢ Icc (-a) a) =
      (eMinus '' ball 0 1 ∪ ePlus '' ball 0 1)ᶜ) :
    let L := h ⁻¹' {k}
    let Lminus : Set L := Subtype.val ⁻¹' (eMinus '' ball 0 1)
    let Lplus : Set L := Subtype.val ⁻¹' (ePlus '' ball 0 1)
    L = (L ∩ eMinus '' ball 0 1) ∪ (L ∩ ePlus '' ball 0 1) ∧
      IsClopen Lminus ∧ IsClopen Lplus ∧
      (∀ x : L, Xor (connectedComponent x ⊆ Lminus) (connectedComponent x ⊆ Lplus)) ∧
      ∃ E : ConnectedComponents L ≃ ConnectedComponents Lminus ⊕ ConnectedComponents Lplus,
        (∀ x : Lminus, E (ConnectedComponents.mk x.val) =
          Sum.inl (ConnectedComponents.mk x)) ∧
        ∀ x : Lplus, E (ConnectedComponents.mk x.val) =
          Sum.inr (ConnectedComponents.mk x) := by
  let L := h ⁻¹' {k}
  let U : Set L := Subtype.val ⁻¹' (eMinus '' ball 0 1)
  let V : Set L := Subtype.val ⁻¹' (ePlus '' ball 0 1)
  have havoid (x : L) : x.val ∉ T '' (univ ×ˢ Icc (-a) a) := by
    rintro ⟨⟨q, t⟩, ht, hTx⟩
    have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
    have heq := hheight q t htε
    rw [hTx] at heq
    have hxlevel : h x.val = k := x.property
    have htc : k - c = t := by linarith
    exact (not_le_of_gt hk) (htc ▸ abs_le.mpr ht.2)
  have hU : IsOpen U :=
    (eMinus.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsMinus)).preimage
      continuous_subtype_val
  have hV : IsOpen V :=
    (ePlus.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsPlus)).preimage
      continuous_subtype_val
  have hUV : Disjoint U V := by
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp hdisjoint
      (image_mono ball_subset_closedBall hx) (image_mono ball_subset_closedBall hy)
  have hcover : U ∪ V = univ := by
    apply eq_univ_of_forall
    intro x
    have hx := havoid x
    rw [hslab] at hx
    exact not_not.mp hx
  refine ⟨?_, component_equiv_of_two_open_pieces hU hV hUV hcover⟩
  ext x
  constructor
  · intro hx
    have hmem : (⟨x, hx⟩ : L) ∈ U ∪ V := hcover.symm ▸ mem_univ _
    rcases hmem with hu | hv
    · exact Or.inl ⟨hx, hu⟩
    · exact Or.inr ⟨hx, hv⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx



theorem card_other_level_components_of_parallel_disks
    {h : S2 → Real} {c ε a k : Real} (haε : a < ε) (hk : a < |k - c|)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hheight : ∀ q t, t ∈ Ioo (-ε) ε → h (T (q, t)) = c + t)
    (eMinus ePlus : OpenPartialHomeomorph E2 S2)
    (hsMinus : closedBall 0 1 ⊆ eMinus.source) (hsPlus : closedBall 0 1 ⊆ ePlus.source)
    (hdisjoint : Disjoint (eMinus '' closedBall 0 1) (ePlus '' closedBall 0 1))
    (hslab : T '' (univ ×ˢ Icc (-a) a) =
      (eMinus '' ball 0 1 ∪ ePlus '' ball 0 1)ᶜ)
    [Finite (ConnectedComponents (h ⁻¹' {k}))] :
    let L := h ⁻¹' {k}
    let Lminus : Set L := Subtype.val ⁻¹' (eMinus '' ball 0 1)
    let Lplus : Set L := Subtype.val ⁻¹' (ePlus '' ball 0 1)
    Finite (ConnectedComponents Lminus) ∧ Finite (ConnectedComponents Lplus) ∧
      Nat.card (ConnectedComponents Lminus) + Nat.card (ConnectedComponents Lplus) =
        Nat.card (ConnectedComponents L) := by
  let L := h ⁻¹' {k}
  let U : Set L := Subtype.val ⁻¹' (eMinus '' ball 0 1)
  let V : Set L := Subtype.val ⁻¹' (ePlus '' ball 0 1)
  obtain ⟨_, _, _, _, E, _⟩ := other_level_components_of_parallel_disks haε hk T hheight
    eMinus ePlus hsMinus hsPlus hdisjoint hslab
  let : Finite (ConnectedComponents U ⊕ ConnectedComponents V) :=
    Finite.of_equiv (ConnectedComponents L) E
  let : Finite (ConnectedComponents U) := Finite.of_injective
    (Sum.inl : ConnectedComponents U → ConnectedComponents U ⊕ ConnectedComponents V)
    Sum.inl_injective
  let : Finite (ConnectedComponents V) := Finite.of_injective
    (Sum.inr : ConnectedComponents V → ConnectedComponents U ⊕ ConnectedComponents V)
    Sum.inr_injective
  refine ⟨inferInstance, inferInstance, ?_⟩
  simpa only [Nat.card_sum] using (Nat.card_congr E).symm

end Poincare.Manifold.Schoenflies
