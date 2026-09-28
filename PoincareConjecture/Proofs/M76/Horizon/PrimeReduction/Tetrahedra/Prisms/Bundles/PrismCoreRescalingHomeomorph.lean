import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.RawPrismRescalingInjection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.CompactRescalingRestriction

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_prism_core_rescaling_homeomorph
    {E ι : Type*} [TopologicalSpace E] [T2Space E] [Finite ι]
    (A B T : ι → Set E) (S : Set E) (hA : ∀j, IsCompact (A j))
    (H : ∀j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ B j)
    (C : ∀j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ T j)
    (hcap : ∀j y, (H j y : E) ∈ S ↔ (y : E × ℝ).2 = 0 ∨ (y : E × ℝ).2 = 1)
    (r : E → E) (hr : ContinuousOn r (⋃j,T j))
    (hrv : ∀j y, r (C j y) = H j y)
    (hinj : InjOn r ((⋃j,T j) \ r ⁻¹' S)) :
    ∃ W : ((⋃j,T j) \ ⋃j,prismEnds (C j) : Set E) ≃ₜ ((⋃j,B j) \ S : Set E),
      (∀x, (W x : E) = r x) ∧
      ∀j (y : B j) (hy : (y : E) ∉ S),
        (W.symm ⟨y,mem_iUnion.mpr ⟨j,y.property⟩,hy⟩ : E) = C j ((H j).symm y) := by
  have hT (j) : IsCompact (T j) := by
    let : CompactSpace (A j ×ˢ I : Set (E × ℝ)) :=
      isCompact_iff_compactSpace.mp ((hA j).prod isCompact_Icc)
    let : CompactSpace (T j) := (C j).compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have himage : r '' (⋃j,T j) = ⋃j,B j := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      have hh := hrv j ((C j).symm ⟨x,hj⟩)
      simp only [(C j).apply_symm_apply] at hh
      exact mem_iUnion.mpr ⟨j,hh ▸ (H j ((C j).symm ⟨x,hj⟩)).property⟩
    · intro hy
      obtain ⟨j,hj⟩ := mem_iUnion.mp hy
      refine ⟨C j ((H j).symm ⟨y,hj⟩),mem_iUnion.mpr ⟨j,(C j _).property⟩,?_⟩
      rw [hrv,(H j).apply_symm_apply]
  have heq : ((⋃j,T j) \ ⋃j,prismEnds (C j)) = (⋃j,T j) \ r ⁻¹' S := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,fun hs => hx.2 ((raw_prism_rescaling_mem_caps_iff A B T S H C hcap r hrv hx.1).mp hs)⟩
    · intro hx
      exact ⟨hx.1,fun hs => hx.2 ((raw_prism_rescaling_mem_caps_iff A B T S H C hcap r hrv hx.1).mpr hs)⟩
  obtain ⟨W,hW⟩ := exists_compact_rescaling_restriction (⋃j,T j) (⋃j,B j) S
    (isCompact_iUnion hT) r hr himage hinj
  let W' := (Homeomorph.setCongr heq).trans W
  have hW' (x) : (W' x : E) = r x := hW _
  refine ⟨W',hW',?_⟩
  intro j y hy
  let x := C j ((H j).symm y)
  have hrx : r x = y := by rw [hrv,(H j).apply_symm_apply]
  have hx : (x : E) ∈ (⋃j,T j) \ ⋃j,prismEnds (C j) := by
    rw [heq]
    exact ⟨mem_iUnion.mpr ⟨j,x.property⟩,by change r x ∉ S; rwa [hrx]⟩
  have hval : W' ⟨x,hx⟩ = ⟨y,mem_iUnion.mpr ⟨j,y.property⟩,hy⟩ :=
    Subtype.ext ((hW' _).trans hrx)
  rw [← hval,W'.symm_apply_apply]

end PoincareConjecture.M76.PrismBelt
