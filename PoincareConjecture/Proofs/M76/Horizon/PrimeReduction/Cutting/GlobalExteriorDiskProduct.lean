import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ExteriorDiskAttachment
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalDiskStripDomain
import PoincareConjecture.Proofs.M76.Wall.OppositePLDomain










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1

theorem PLDomain.interior_removal_geometry
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (hRPL : PLDomain e R) (hDPL : PLDomain e D)
    (hDR : D ⊆ interior R) :
    IsCompact (R ∩ (interior D)ᶜ) ∧ PLDomain e (R ∩ (interior D)ᶜ) ∧
      (R ∩ (interior D)ᶜ) ∪ D = R ∧
      (R ∩ (interior D)ᶜ) ∩ D = frontier D ∧
      frontier (R ∩ (interior D)ᶜ) = frontier D ∪ frontier R := by
  obtain ⟨hop, hfront⟩ := hDPL.compl_interior
  have hbound : frontier (interior D)ᶜ ⊆ interior R := by
    rw [hfront]
    exact hDPL.closed.frontier_subset.trans hDR
  have houtside : frontier R ⊆ (interior D)ᶜ := by
    intro x hx hxD
    exact hx.2 (hDR (interior_subset hxD))
  refine ⟨hR.inter_right isOpen_interior.isClosed_compl,
    hRPL.inter_of_frontier_subset_interior hop hbound, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · exact union_subset inter_subset_left (hDR.trans interior_subset)
    · intro x hx
      by_cases hxD : x ∈ D
      · exact Or.inr hxD
      · exact Or.inl ⟨hx, fun hi => hxD (interior_subset hi)⟩
  · rw [hDPL.closed.frontier_eq]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩,
      fun hx => ⟨⟨interior_subset (hDR hx.1), hx.2⟩, hx.1⟩⟩
  · rw [frontier_inter_of_frontier_subset_interior hRPL.closed hop.closed hbound,
      hfront, inter_eq_left.mpr houtside]

theorem OriginalDiskProduct.exists_global_exterior_product
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R H K L : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j)
    (hR : IsCompact R) (hRPL : PLDomain e R) (hHPL : PLDomain e H)
    (hKPL : PLDomain e K) (hKH : K ⊆ interior H) (hKR : K ⊆ interior R)
    (hL : L = H ∩ (interior K)ᶜ)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior H ∩ interior R))
    (hopen : IsOpen ((Subtype.val : L → X) ⁻¹' P.openStrip)) :
    ∃ G : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j,
      G.map = P.map ∧ G.closedStrip = P.closedStrip ∧ G.openStrip = P.openStrip ∧
      G.endDisks = P.endDisks ∧
      IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' G.openStrip) := by
  obtain ⟨hop, hfront⟩ := hKPL.compl_interior
  have hfrontH : frontier L = frontier K ∪ (frontier H ∩ (interior K)ᶜ) := by
    rw [hL, frontier_inter_of_frontier_subset_interior hHPL.closed hop.closed]
    · rw [hfront]
    · rw [hfront]
      exact hKPL.closed.frontier_subset.trans hKH
  have hfrontR := (hRPL.interior_removal_geometry hR hKPL hKR).2.2.2.2
  have hmapfront (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ Icc (-1 : ℝ) 1) :
      P.map z ∈ frontier (R ∩ (interior K)ᶜ) ↔ P.map z ∈ frontier L := by
    rw [hfrontR, hfrontH]
    simp only [mem_union, mem_inter_iff]
    have hnR : P.map z ∉ frontier R := fun hx => hx.2 (hsmall hz).2
    have hnH : P.map z ∉ frontier H := fun hx => hx.2 (hsmall hz).1
    simp only [hnR, hnH, false_and, or_false]
  let G : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j :=
    { map := P.map
      polyhedral := P.polyhedral
      injective := P.injective
      embedding := P.embedding
      inside := fun z hz => ⟨interior_subset (hsmall hz).2, (hL.subset (P.inside hz)).2⟩
      central := P.central
      proper := fun z hz => (hmapfront z hz).trans (P.proper z hz) }
  refine ⟨G, rfl, rfl, rfl, rfl, ?_⟩
  obtain ⟨U, hU, hUeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hopen
  have heq : (Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' G.openStrip =
      (Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' (U ∩ interior H) := by
    ext x
    constructor
    · intro hx
      have hxL : (x : X) ∈ L := P.closedStrip_subset
        (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self) hx)
      have hxU : (⟨x, hxL⟩ : L) ∈ (Subtype.val : L → X) ⁻¹' U := by
        rw [hUeq]
        exact hx
      obtain ⟨z, hz, hzx⟩ := hx
      have hzfull : z ∈ Disk ×ˢ Icc (-1 : ℝ) 1 := by
        exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
      exact ⟨hxU, hzx ▸ (hsmall hzfull).1⟩
    · intro hx
      have hxL : (x : X) ∈ L := hL.symm.subset ⟨interior_subset hx.2, x.property.2⟩
      have hxU : (⟨x, hxL⟩ : L) ∈ (Subtype.val : L → X) ⁻¹' U := hx.1
      rw [hUeq] at hxU
      exact hxU
  rw [heq]
  exact (hU.inter isOpen_interior).preimage continuous_subtype_val

theorem OriginalDiskProduct.global_common_cut_geometry
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R H K L : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j)
    (hR : IsCompact R) (hRPL : PLDomain e R)
    (hDPL : PLDomain e (K ∪ P.closedStrip)) (hKR : K ⊆ interior R)
    (hL : L = H ∩ (interior K)ᶜ)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R))
    (hfront : frontier (K ∪ P.closedStrip) =
      (frontier K \ P.openStrip) ∪ P.endDisks) :
    let Q := R ∩ (interior (K ∪ P.closedStrip))ᶜ
    interior (K ∪ P.closedStrip) = interior K ∪ P.openStrip ∧
    Q = (R ∩ (interior K)ᶜ) \ P.openStrip ∧
    IsCompact Q ∧ PLDomain e Q ∧
    Q ∪ (K ∪ P.closedStrip) = R ∧
    Q ∩ (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks ∧
    frontier Q = ((frontier K \ P.openStrip) ∪ P.endDisks) ∪ frontier R ∧
    Q ∪ P.closedStrip = R ∩ (interior K)ᶜ ∧
    Q ∩ P.closedStrip = P.endDisks := by
  have hstripR : P.closedStrip ⊆ interior R := by
    rintro x ⟨z, hz, rfl⟩
    exact hsmall ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hstripout : P.closedStrip ⊆ (interior K)ᶜ := by
    intro x hx
    exact (hL.subset (P.closedStrip_subset hx)).2
  have hopenclosed : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hends : P.endDisks = P.closedStrip \ P.openStrip :=
    P.closedStrip_sdiff_openStrip.symm
  have hinside : interior (K ∪ P.closedStrip) = interior K ∪ P.openStrip := by
    apply Subset.antisymm
    · intro x hx
      rcases (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed.interior_union_right hx with
        hxK | hxS
      · exact Or.inl hxK
      · by_cases hxO : x ∈ P.openStrip
        · exact Or.inr hxO
        · have hxF : x ∈ frontier (K ∪ P.closedStrip) :=
            hfront.symm.subset (Or.inr (hends.symm.subset ⟨hxS, hxO⟩))
          exact False.elim (hxF.2 hx)
    · apply union_subset (interior_mono subset_union_left)
      intro x hx
      apply (mem_interior_iff_notMem_frontier
        (show x ∈ K ∪ P.closedStrip from Or.inr (hopenclosed hx))).mpr
      rw [hfront]
      rintro (hxK | hxE)
      · exact hxK.2 hx
      · exact (hends.subset hxE).2 hx
  have hQeq : R ∩ (interior (K ∪ P.closedStrip))ᶜ =
      (R ∩ (interior K)ᶜ) \ P.openStrip := by
    rw [hinside]
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_union, mem_sdiff, not_or]
    tauto
  obtain ⟨hQcompact, hQPL, hreconstruct, hattach, hQfront⟩ :=
    hRPL.interior_removal_geometry hR hDPL (union_subset hKR hstripR)
  refine ⟨hinside, hQeq, hQcompact, hQPL, hreconstruct, hattach.trans hfront,
    hQfront.trans (congrArg (fun S => S ∪ frontier R) hfront), ?_, ?_⟩
  · rw [hQeq]
    apply Subset.antisymm
    · exact union_subset sdiff_subset (fun x hx => ⟨interior_subset (hstripR hx), hstripout hx⟩)
    · intro x hx
      by_cases hxO : x ∈ P.openStrip
      · exact Or.inr (hopenclosed hxO)
      · exact Or.inl ⟨hx, hxO⟩
  · rw [hQeq, hends]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩,
      fun hx => ⟨⟨⟨interior_subset (hstripR hx.1), hstripout hx.1⟩, hx.2⟩, hx.1⟩⟩

end PoincareConjecture.M76
