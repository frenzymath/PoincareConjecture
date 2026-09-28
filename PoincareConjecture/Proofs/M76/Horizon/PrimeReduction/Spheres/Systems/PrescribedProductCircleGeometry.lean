import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem OriginalDiskProduct.positioned_circle_contact_geometry
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S F circle : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (ret : Bool → Set X)
    (hretDis : Disjoint (ret true) (ret false))
    (hretContact : ∀ b, ret b ∩ P.closedStrip = P.capRimSet b)
    (hcover : (ret true ∪ ret false) ∪ P.map '' (Rim ×ˢ J) = S)
    (hproper : ∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, P.map z ∈ S ↔ z.1 ∈ Rim)
    (hcapF : ∀ b, Disjoint (P.capDisk b) F)
    (hbandF : (P.map '' (Rim ×ˢ J)) ∩ F = circle) :
    Disjoint (ret true ∪ P.capDisk true) (ret false ∪ P.capDisk false) ∧
      ((ret true ∪ P.capDisk true) ∪ (ret false ∪ P.capDisk false)) \ P.closedStrip =
        S \ P.closedStrip ∧
      ((ret true ∪ P.capDisk true) ∪ (ret false ∪ P.capDisk false)) ∩ F =
        (S ∩ F) \ circle ∧
      P.closedStrip ∩ (S ∩ F) = circle ∧
      IsCompact P.closedStrip := by
  have hcapStrip (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply Subset.trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hbandStrip : P.map '' (Rim ×ˢ J) ⊆ P.closedStrip :=
    image_mono (prod_mono sphere_subset_closedBall subset_rfl)
  have hretS (b : Bool) : ret b ⊆ S := by
    intro x hx
    apply hcover.subset
    cases b
    · exact Or.inl (Or.inr hx)
    · exact Or.inl (Or.inl hx)
  have hretCap (b : Bool) : Disjoint (ret b) (P.capDisk (!b)) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp (P.disjoint_capDisks b)
      (P.capRimSet_subset_capDisk b ((hretContact b).subset ⟨hx,hcapStrip (!b) hy⟩)) hy
  have hstripS : P.closedStrip ∩ S = P.map '' (Rim ×ˢ J) := by
    apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hs⟩
      have hzI : z ∈ Disk ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
      exact ⟨z,⟨(hproper z hzI).mp hs,hz.2⟩,rfl⟩
    · intro x hx
      exact ⟨hbandStrip hx,hcover.subset (Or.inr hx)⟩
  have hretCircle (b : Bool) : Disjoint (ret b) circle := by
    apply disjoint_left.mpr
    intro x hx hc
    have hh := hbandF.symm.subset hc
    exact disjoint_left.mp (hcapF b)
      (P.capRimSet_subset_capDisk b ((hretContact b).subset ⟨hx,hbandStrip hh.1⟩)) hh.2
  refine ⟨disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hretDis,hretCap true⟩,
    disjoint_union_right.mpr ⟨(hretCap false).symm,P.disjoint_capDisks true⟩⟩,?_,?_,?_,
    P.isCompact_closed_strip (by norm_num : (1/2 : ℝ) ≤ 1)⟩
  · ext x
    constructor
    · rintro ⟨(hx | hx),hout⟩ <;> rcases hx with hx | hx
      · exact ⟨hretS true hx,hout⟩
      · exact (hout (hcapStrip true hx)).elim
      · exact ⟨hretS false hx,hout⟩
      · exact (hout (hcapStrip false hx)).elim
    · rintro ⟨hx,hout⟩
      rcases hcover.symm.subset hx with (hx | hx) | hx
      · exact ⟨Or.inl (Or.inl hx),hout⟩
      · exact ⟨Or.inr (Or.inl hx),hout⟩
      · exact (hout (hbandStrip hx)).elim
  · ext x
    constructor
    · rintro ⟨(hx | hx),hF⟩ <;> rcases hx with hx | hx
      · exact ⟨⟨hretS true hx,hF⟩,fun hc => disjoint_left.mp (hretCircle true) hx hc⟩
      · exact (disjoint_left.mp (hcapF true) hx hF).elim
      · exact ⟨⟨hretS false hx,hF⟩,fun hc => disjoint_left.mp (hretCircle false) hx hc⟩
      · exact (disjoint_left.mp (hcapF false) hx hF).elim
    · rintro ⟨⟨hx,hF⟩,hout⟩
      rcases hcover.symm.subset hx with (hx | hx) | hx
      · exact ⟨Or.inl (Or.inl hx),hF⟩
      · exact ⟨Or.inr (Or.inl hx),hF⟩
      · exact (hout (hbandF.subset ⟨hx,hF⟩)).elim
  · rw [← inter_assoc,hstripS,hbandF]

end PoincareConjecture.M76
