import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76
local notation "J" => Icc (-1 : ℝ) 1

theorem exists_short_relative_inward_strip
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set Y} (hS : IsCompact S) {N O : Set X}
    (c : Y × ℝ → X) (hc : ContinuousOn c (S ×ˢ J))
    (H : (S ×ˢ J) ≃ₜ (c '' (S ×ˢ J)))
    (hH : ∀ z : (S ×ˢ J), (H z : X) = c z)
    (hO : IsOpen O) (hzero : ∀ z ∈ S,c (z,0) ∈ O)
    (hcover : O ∩ N ⊆ c '' (S ×ˢ J))
    (hsign : ∀ z ∈ S ×ˢ J,c z ∈ N ↔ 0 ≤ z.2) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧
      c '' (S ×ˢ Icc (-δ) δ) ⊆ O ∧
      IsOpen ((Subtype.val : N → X) ⁻¹' (c '' (S ×ˢ Ico 0 δ))) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hcc : Continuous (fun z : S × J => c ((z.1 : Y),(z.2 : ℝ))) :=
    hc.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨z.1.property,z.2.property⟩)
  obtain ⟨δ,hδ,hδsmall,hthin⟩ := hcc.exists_closed_strip_subset hO
    (fun z => hzero z z.property)
  have hshort : c '' (S ×ˢ Icc (-δ) δ) ⊆ O := by
    rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
    have htJ : t ∈ J := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    exact hthin ⟨z,hz⟩ ⟨t,htJ⟩ (abs_le.mpr ht)
  let height : C(c '' (S ×ˢ J),ℝ) :=
    ⟨fun x => ((H.symm x : Y × ℝ).2),
      continuous_snd.comp (continuous_subtype_val.comp H.symm.continuous)⟩
  have hheight (z : Y × ℝ) (hz : z ∈ S ×ˢ J) :
      height ⟨c z,mem_image_of_mem c hz⟩ = z.2 := by
    have hh : (⟨c z,mem_image_of_mem c hz⟩ : c '' (S ×ˢ J)) = H ⟨z,hz⟩ :=
      Subtype.ext (hH ⟨z,hz⟩).symm
    change ((H.symm _ : Y × ℝ).2) = z.2
    rw [hh,H.symm_apply_apply]
  obtain ⟨V,hV,hVe⟩ := isOpen_induced_iff.mp
    (isOpen_Iio.preimage height.continuous : IsOpen (height ⁻¹' Iio δ))
  have hVtest (x : X) (hx : x ∈ c '' (S ×ˢ J)) :
      x ∈ V ↔ height ⟨x,hx⟩ < δ := by
    change (⟨x,hx⟩ : c '' (S ×ˢ J)) ∈ Subtype.val ⁻¹' V ↔ _
    rw [hVe]
    rfl
  have heq : (Subtype.val : N → X) ⁻¹' (c '' (S ×ˢ Ico 0 δ)) =
      (Subtype.val : N → X) ⁻¹' (O ∩ V) := by
    ext x
    constructor
    · rintro ⟨⟨z,t⟩,⟨hz,ht⟩,hcx⟩
      have htJ : t ∈ J := ⟨by linarith [ht.1],by linarith [ht.2]⟩
      have hcim : c (z,t) ∈ c '' (S ×ˢ J) := mem_image_of_mem c ⟨hz,htJ⟩
      change (x : X) ∈ O ∩ V
      rw [←hcx]
      exact ⟨hshort ⟨(z,t),⟨hz,by linarith [ht.1],ht.2.le⟩,rfl⟩,
        (hVtest _ hcim).mpr (by rw [hheight _ ⟨hz,htJ⟩]; exact ht.2)⟩
    · rintro ⟨hxO,hxV⟩
      obtain ⟨z,hz,hzx⟩ := hcover ⟨hxO,x.property⟩
      have hzN : c z ∈ N := hzx.symm ▸ x.property
      have hzV : c z ∈ V := hzx.symm ▸ hxV
      have hlt := (hVtest _ (mem_image_of_mem c hz)).mp hzV
      rw [hheight z hz] at hlt
      exact ⟨z,⟨hz.1,(hsign z hz).mp hzN,hlt⟩,hzx⟩
  exact ⟨δ,hδ,hδsmall,hshort,heq ▸ ((hO.inter hV).preimage continuous_subtype_val)⟩

end PoincareConjecture.M76
