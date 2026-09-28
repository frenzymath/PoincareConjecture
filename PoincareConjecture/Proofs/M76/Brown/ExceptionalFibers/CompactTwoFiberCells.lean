import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.TwoFiberCellNeighborhoods

set_option autoImplicit false

open Set Topology

namespace ContinuousMap

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [Infinite E] [TopologicalSpace X] [T2Space X] [RegularSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]

theorem exists_compact_second_fiber_ballPair_subset (q : C(X, Y))
    (hq : Function.Surjective q) (a b : Y) (hab : a ≠ b)
    (hfib : ∀ x y, q x = q y ↔ x = y ∨
      (q x = a ∧ q y = a) ∨ (q x = b ∧ q y = b))
    (p : X) (hpa : q p ≠ a) (hpb : q p ≠ b)
    (C : OpenPartialHomeomorph X E) (hCs : C.source = {p}ᶜ) (hCt : C.target = univ)
    (D : OpenPartialHomeomorph Y E) (hDs : D.source = {q p}ᶜ) (hDt : D.target = univ)
    {U : Set X} (hU : IsOpen U) (hBU : q ⁻¹' {b} ⊆ U) :
    ∃ K : Set X, IsCompact K ∧ q ⁻¹' {b} ⊆ interior K ∧ K ⊆ U ∧
      IsUnitBallPair E K (frontier K) := by
  let T : Set Y := {q p}ᶜ
  let N : Set X := q ⁻¹' T
  have hT : IsOpen T := isClosed_singleton.isOpen_compl
  have hN : IsOpen N := hT.preimage q.continuous
  have hNeq : N = {p}ᶜ := by
    ext x
    change (q x ≠ q p) ↔ x ≠ p
    constructor
    · intro hx hxp
      exact hx (congrArg q hxp)
    · intro hx he
      rcases (hfib x p).mp he with hxp | hA | hB
      · exact hx hxp
      · exact hpa hA.2
      · exact hpb hB.2
  have hAN : q ⁻¹' {a} ⊆ N := by
    intro x hx he
    exact hpa (he.symm.trans hx)
  have hBN : q ⁻¹' {b} ⊆ N := by
    intro x hx he
    exact hpb (he.symm.trans hx)
  let aT : T := ⟨a, hpa.symm⟩
  let bT : T := ⟨b, hpb.symm⟩
  let qN : C(N, T) := q.restrictPreimage T
  have hqN : IsQuotientMap qN :=
    (q.continuous.isClosedMap.isQuotientMap q.continuous hq).restrictPreimage_isOpen hT
  have habT : aT ≠ bT := fun he => hab (congrArg Subtype.val he)
  have hfibN (x y : N) : qN x = qN y ↔ x = y ∨
      (qN x = aT ∧ qN y = aT) ∨ (qN x = bT ∧ qN y = bT) := by
    simp only [Subtype.ext_iff]
    change (q (x : X) = q (y : X)) ↔ (x : X) = (y : X) ∨
      (q (x : X) = a ∧ q (y : X) = a) ∨ (q (x : X) = b ∧ q (y : X) = b)
    exact hfib (x : X) (y : X)
  have hANrange : q ⁻¹' {a} ⊆ range (Subtype.val : N → X) := by
    intro x hx
    exact ⟨⟨x, hAN hx⟩, rfl⟩
  have hBNrange : q ⁻¹' {b} ⊆ range (Subtype.val : N → X) := by
    intro x hx
    exact ⟨⟨x, hBN hx⟩, rfl⟩
  have hpreA : qN ⁻¹' {aT} = (Subtype.val : N → X) ⁻¹' (q ⁻¹' {a}) := by
    ext x
    exact Subtype.ext_iff
  have hpreB : qN ⁻¹' {bT} = (Subtype.val : N → X) ⁻¹' (q ⁻¹' {b}) := by
    ext x
    exact Subtype.ext_iff
  have hAc : IsCompact (qN ⁻¹' {aT}) := by
    rw [hpreA]
    exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (isClosed_singleton.preimage q.continuous).isCompact hANrange
  have hBc : IsCompact (qN ⁻¹' {bT}) := by
    rw [hpreB]
    exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (isClosed_singleton.preimage q.continuous).isCompact hBNrange
  let CN : N ≃ₜ E :=
    ((Homeomorph.setCongr (hNeq.trans hCs.symm)).trans C.toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr hCt).trans (Homeomorph.Set.univ E))
  let DT : T ≃ₜ E :=
    ((Homeomorph.setCongr hDs.symm).trans D.toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr hDt).trans (Homeomorph.Set.univ E))
  have hUN : IsOpen ((Subtype.val : N → X) ⁻¹' U) := hU.preimage continuous_subtype_val
  have hBUN : qN ⁻¹' {bT} ⊆ (Subtype.val : N → X) ⁻¹' U := by
    intro x hx
    exact hBU (congrArg Subtype.val hx)
  obtain ⟨K, hK, hBK, hKU, hKpair⟩ := qN.exists_second_fiber_ballPair_subset
    hqN aT bT habT hfibN hAc hBc CN.toOpenPartialHomeomorph rfl rfl
      DT.toOpenPartialHomeomorph rfl rfl hUN hBUN
  obtain ⟨xb, hxb⟩ := hq b
  let : Nonempty N := ⟨⟨xb, hBN hxb⟩⟩
  let L : OpenPartialHomeomorph N X :=
    hN.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  have hLs : L.source = univ := rfl
  have hLsmem (x : N) : x ∈ L.source := hLs.symm ▸ mem_univ x
  obtain ⟨hLK, hLKpair⟩ := L.image_compact_ballPair hK (fun x _ => hLsmem x) hKpair
  have hLI : IsOpen (L '' interior K) :=
    L.isOpen_image_of_subset_source isOpen_interior (fun x _ => hLsmem x)
  have hLIK : L '' interior K ⊆ interior (L '' K) :=
    interior_maximal (image_mono interior_subset) hLI
  refine ⟨L '' K, hLK, ?_, ?_, hLKpair⟩
  · intro x hx
    let xN : N := ⟨x, hBN hx⟩
    have hxK : xN ∈ interior K := hBK (Subtype.ext hx)
    exact hLIK ⟨xN, hxK, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hKU hy

end ContinuousMap
