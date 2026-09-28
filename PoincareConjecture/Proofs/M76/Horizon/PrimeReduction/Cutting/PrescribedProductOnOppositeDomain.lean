import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PrescribedProductOpenness
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.WholeDiskProductOnOppositeDomain
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductOpenSubsets









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_prescribed_product_on_opposite_domain
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K S B : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hK : IsCompact K) (hKPL : PLDomain e K)
    (hKR : K ⊆ interior R) (hBS : Disjoint B S) (hfront : frontier K = B ∪ S)
    (p : V2 × ℝ → X) (hp : PolyhedralPLInCharts e p (Disk ×ˢ I))
    (hpi : InjOn p (Disk ×ˢ I)) (hpR : MapsTo p (Disk ×ˢ I) (interior R))
    (hpS : ∀ z ∈ Disk ×ˢ I, p z ∈ S ↔ z.1 ∈ Rim)
    (hcontact : K ∩ (p '' (Disk ×ˢ I)) = p '' (Rim ×ˢ I)) :
    ∃ P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) (fun z => p (z,0)),
      P.map = p ∧ MapsTo P.map (Disk ×ˢ I) (interior R ∩ Bᶜ) ∧
      IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' P.openStrip) ∧
      IsCompact P.cutCarrier ∧ PLDomain e P.cutCarrier ∧
      P.closedStrip ∩ K = P.map '' (Rim ×ˢ J) ∧
      IsCompact (K ∪ P.closedStrip) ∧ PLDomain e (K ∪ P.closedStrip) ∧
      frontier (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹'
          (P.map '' (Disk ×ˢ Ioo (-η) η))) ∧
        IsOpen ((Subtype.val : S → X) ⁻¹'
          (P.map '' (Rim ×ˢ Ioo (-η) η))) := by
  obtain ⟨hL,hLPL,_,hmeet,hLfront⟩ := he.interior_removal_geometry hR hKPL hKR
  have hpK (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ I) : p z ∉ interior K := by
    intro hzK
    obtain ⟨w,hw,heq⟩ := hcontact.subset ⟨interior_subset hzK,⟨z,hz,rfl⟩⟩
    have hzS : p z ∈ S := heq ▸ (hpS w ⟨sphere_subset_closedBall hw.1,hw.2⟩).mpr hw.1
    exact (hfront.symm.subset (Or.inr hzS)).2 hzK
  have hpB : Disjoint (p '' (Disk ×ˢ I)) B := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hxB
    have hxK := hKPL.closed.frontier_subset (hfront.symm.subset (Or.inl hxB))
    obtain ⟨w,hw,heq⟩ := hcontact.subset ⟨hxK,⟨z,hz,rfl⟩⟩
    exact disjoint_left.mp hBS hxB
      (heq ▸ (hpS w ⟨sphere_subset_closedBall hw.1,hw.2⟩).mpr hw.1)
  have hpL : MapsTo p (Disk ×ˢ I) (R ∩ (interior K)ᶜ) :=
    fun z hz => ⟨interior_subset (hpR hz),hpK z hz⟩
  have hproper (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ I) :
      p z ∈ frontier (R ∩ (interior K)ᶜ) ↔ z.1 ∈ Rim := by
    rw [hLfront,hfront]
    constructor
    · rintro ((hzB | hzS) | hzR)
      · exact False.elim (disjoint_left.mp hpB ⟨z,hz,rfl⟩ hzB)
      · exact (hpS z hz).mp hzS
      · exact False.elim (hzR.2 (hpR hz))
    · intro hzr
      exact Or.inl (Or.inr ((hpS z hz).mpr hzr))
  letI : CompactSpace (Disk ×ˢ I : Set (V2 × ℝ)) :=
    isCompact_iff_compactSpace.mp ((isCompact_closedBall _ _).prod isCompact_Icc)
  let P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) (fun z => p (z,0)) := {
    map := p
    polyhedral := hp
    injective := hpi
    embedding := hp.continuousOn.domRestrict.isClosedEmbedding
      (fun z w hzw => Subtype.ext (hpi z.property w.property hzw))
    inside := hpL
    central := fun _ _ => rfl
    proper := hproper }
  have hfull := hLPL.isOpen_original_proper_product zero_lt_one p hp hpi hpL hproper
  have hcollars (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
      IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹'
        (P.map '' (Disk ×ˢ Ioo (-η) η))) ∧
      IsOpen ((Subtype.val : frontier (R ∩ (interior K)ᶜ) → X) ⁻¹'
        (P.map '' (Rim ×ˢ Ioo (-η) η))) := by
    have hopen : IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹'
        (P.map '' (Disk ×ˢ Ioo (-η) η))) := by
      apply P.isOpen_image_parameter_subset hfull
      · intro z hz
        exact ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
      · convert isOpen_Ioo.preimage
          (continuous_snd.comp (continuous_subtype_val :
            Continuous (Subtype.val : (Disk ×ˢ I : Set (V2 × ℝ)) → V2 × ℝ))) using 1
        ext z
        exact and_iff_right z.property.1
    exact ⟨hopen,P.isOpen_lateral_image hL.isClosed hη1 hopen⟩
  have hopen := (hcollars (1/2) (by norm_num) (by norm_num)).1
  obtain ⟨hcut,hint,hcutfront,hoverlap,_,_⟩ := P.cut_geometry hL hopen
  have hcutPL := P.plDomain_cut hL hLPL hopen
  have hstrip : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J) := by
    apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hzK⟩
      have hzfull : z ∈ Disk ×ˢ I :=
        ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
      have hzfront : P.map z ∈ frontier K := hmeet.subset ⟨P.inside hzfull,hzK⟩
      exact ⟨z,⟨(P.proper z hzfull).mp (hLfront.symm.subset (Or.inl hzfront)),hz.2⟩,rfl⟩
    · rintro _ ⟨z,hz,rfl⟩
      have hzfull : z ∈ Disk ×ˢ I := ⟨sphere_subset_closedBall hz.1,
        by constructor <;> linarith [hz.2.1,hz.2.2]⟩
      exact ⟨⟨z,⟨sphere_subset_closedBall hz.1,hz.2⟩,rfl⟩,
        hKPL.closed.frontier_subset (hfront.symm.subset (Or.inr ((hpS z hzfull).mpr hz.1)))⟩
  have hfrontR : frontier R ∩ (interior K)ᶜ = frontier R := by
    apply inter_eq_left.mpr
    intro x hx hxK
    exact hx.2 (hKR (interior_subset hxK))
  have hLfront' :
      frontier (R ∩ (interior K)ᶜ) = frontier K ∪ (frontier R ∩ (interior K)ᶜ) := by
    rwa [hfrontR]
  have hstripR : P.closedStrip ⊆ interior R := by
    rintro x ⟨z,hz,rfl⟩
    exact hpR ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  obtain ⟨hDPL,hDc,_,_,hDfront,_⟩ := P.exterior_attachment_geometry_with_collars
    hKPL hK hKR rfl hLfront' hstripR hcutPL hint hcutfront hoverlap hcollars
  refine ⟨P,rfl,(fun z hz => ⟨hpR hz,fun hb => disjoint_left.mp hpB ⟨z,hz,rfl⟩ hb⟩),
    hopen,hcut,hcutPL,hstrip,hDc,hDPL,hDfront,?_⟩
  intro η hη hη1
  refine ⟨(hcollars η hη hη1).1,?_⟩
  have hSfront : S ⊆ frontier (R ∩ (interior K)ᶜ) := fun x hx =>
    hLfront.symm.subset (Or.inl (hfront.symm.subset (Or.inr hx)))
  exact ((hcollars η hη hη1).2).preimage (continuous_inclusion hSfront)

end PoincareConjecture.M76
