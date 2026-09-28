import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalWholeDiskProduct
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ExteriorDiskAttachment

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem exists_whole_disk_product_on_opposite_domain
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K S B V : Set X} {k : V2 → X}
    (hR : IsCompact R) (he : PLDomain e R) (hK : IsCompact K) (hKPL : PLDomain e K)
    (hKR : K ⊆ interior R) (sB : ChartwisePLSphere e B)
    (hBS : Disjoint B S) (hfront : frontier K = B ∪ S)
    (hcontact : K ∩ (k '' Disk) = k '' Rim)
    (hk : PolyhedralPLInCharts e k Disk)
    (hkemb : Topology.IsEmbedding (fun z : Disk => k z))
    (hkR : MapsTo k Disk (interior R))
    (hkS : ∀ z ∈ Disk, k z ∈ S ↔ z ∈ Rim)
    (hV : IsOpen V) (hkV : k '' Disk ⊆ V) :
    ∃ P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) k,
      MapsTo P.map (Disk ×ˢ I) (V ∩ interior R ∩ Bᶜ) ∧
      (∀ z ∈ Disk ×ˢ I, P.map z ∈ S ↔ z.1 ∈ Rim) ∧
      IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' P.openStrip) ∧
      IsCompact P.cutCarrier ∧ PLDomain e P.cutCarrier ∧
      P.closedStrip ∩ K = P.map '' (Rim ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) ∧
      IsCompact (K ∪ P.closedStrip) ∧ PLDomain e (K ∪ P.closedStrip) ∧
      frontier (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹'
          (P.map '' (Disk ×ˢ Ioo (-η) η))) ∧
        IsOpen ((Subtype.val : S → X) ⁻¹'
          (P.map '' (Rim ×ˢ Ioo (-η) η))) := by
  obtain ⟨hL,hLPL,_,hmeet,hLfront⟩ := he.interior_removal_geometry hR hKPL hKR
  have hkK (z : V2) (hz : z ∈ Disk) : k z ∉ interior K := by
    intro hzK
    obtain ⟨w,hw,heq⟩ := hcontact.subset ⟨interior_subset hzK,⟨z,hz,rfl⟩⟩
    have hzS : k z ∈ S := heq ▸ (hkS w (sphere_subset_closedBall hw)).mpr hw
    exact (hfront.symm.subset (Or.inr hzS)).2 hzK
  have hkB : Disjoint (k '' Disk) B := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hxB
    have hxK := hKPL.closed.frontier_subset (hfront.symm.subset (Or.inl hxB))
    obtain ⟨w,hw,heq⟩ := hcontact.subset ⟨hxK,⟨z,hz,rfl⟩⟩
    exact disjoint_left.mp hBS hxB (heq ▸ (hkS w (sphere_subset_closedBall hw)).mpr hw)
  have hkL : MapsTo k Disk (R ∩ (interior K)ᶜ) := fun z hz => ⟨interior_subset (hkR hz),hkK z hz⟩
  have hkproper (z : Disk) : k z ∈ frontier (R ∩ (interior K)ᶜ) ↔ (z : V2) ∈ Rim := by
    rw [hLfront,hfront]
    constructor
    · rintro ((hzB | hzS) | hzR)
      · exact False.elim (disjoint_left.mp hkB ⟨z,z.property,rfl⟩ hzB)
      · exact (hkS z z.property).mp hzS
      · exact False.elim (hzR.2 (hkR z.property))
    · intro hz
      exact Or.inl (Or.inr ((hkS z z.property).mpr hz))
  have hsmallOpen : IsOpen (V ∩ interior R ∩ Bᶜ) :=
    (hV.inter isOpen_interior).inter sB.isCompact.isClosed.isOpen_compl
  have hkSmall : k '' Disk ⊆ V ∩ interior R ∩ Bᶜ := by
    intro x hx
    exact ⟨⟨hkV hx,by obtain ⟨z,hz,rfl⟩ := hx; exact hkR hz⟩,
      fun hxB => disjoint_left.mp hkB hx hxB⟩
  obtain ⟨P,hPsmall,hopen,hcutPL,hcut,hint,hcutfront,hoverlap,_,_,hcollars⟩ :=
    exists_original_disk_cut_domain_with_collars hL hLPL hk hkemb hkL hkproper hsmallOpen hkSmall
  have hmark (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ I) : P.map z ∈ S ↔ z.1 ∈ Rim := by
    rw [←P.proper z hz,hLfront,hfront]
    exact ⟨fun h => Or.inl (Or.inr h),fun h => h.elim
      (fun h => h.elim (fun hb => False.elim ((hPsmall hz).2 hb)) id)
      (fun hr => False.elim (hr.2 (hPsmall hz).1.2))⟩
  have hstrip : P.closedStrip ∩ K = P.map '' (Rim ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hzK⟩
      have hzfull : z ∈ Disk ×ˢ I := ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
      have hzfront : P.map z ∈ frontier K := hmeet.subset ⟨P.inside hzfull,hzK⟩
      exact ⟨z,⟨(P.proper z hzfull).mp (hLfront.symm.subset (Or.inl hzfront)),hz.2⟩,rfl⟩
    · rintro _ ⟨z,hz,rfl⟩
      have hzfull : z ∈ Disk ×ˢ I := ⟨sphere_subset_closedBall hz.1,
        by constructor <;> linarith [hz.2.1,hz.2.2]⟩
      exact ⟨⟨z,⟨sphere_subset_closedBall hz.1,hz.2⟩,rfl⟩,
        hKPL.closed.frontier_subset (hfront.symm.subset (Or.inr ((hmark z hzfull).mpr hz.1)))⟩
  have hfrontR : frontier R ∩ (interior K)ᶜ = frontier R := by
    apply inter_eq_left.mpr
    intro x hx hxK
    exact hx.2 (hKR (interior_subset hxK))
  have hLfront' : frontier (R ∩ (interior K)ᶜ) = frontier K ∪ (frontier R ∩ (interior K)ᶜ) := by
    rwa [hfrontR]
  have hstripR : P.closedStrip ⊆ interior R := by
    rintro x ⟨z,hz,rfl⟩
    exact (hPsmall ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩).1.2
  obtain ⟨hDPL,hDc,_,_,hDfront,_⟩ := P.exterior_attachment_geometry_with_collars
    hKPL hK hKR rfl hLfront' hstripR hcutPL hint hcutfront hoverlap hcollars
  refine ⟨P,hPsmall,hmark,hopen,hcut,hcutPL,hstrip,hDc,hDPL,hDfront,?_⟩
  intro η hη hη1
  refine ⟨(hcollars η hη hη1).1,?_⟩
  have hSfront : S ⊆ frontier (R ∩ (interior K)ᶜ) := fun x hx =>
    hLfront.symm.subset (Or.inl (hfront.symm.subset (Or.inr hx)))
  exact ((hcollars η hη hη1).2).preimage (continuous_inclusion hSfront)

end PoincareConjecture.M76
