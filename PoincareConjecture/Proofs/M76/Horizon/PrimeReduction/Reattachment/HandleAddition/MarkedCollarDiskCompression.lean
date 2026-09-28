import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.MarkedCollarCompressionHomotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalFiniteInwardCompression
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.OriginalFiniteCollarModel
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem compress_original_disk_preserving_product_mark
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (M : OriginalFiniteCollarModel e R)
    (hmark : ∀ z ∈ M.collarBase.space ×ˢ I,
      (M.inverse (M.collar z) : X) ∈ S ↔ (M.inverse (M.collar (z.1,0)) : X) ∈ S)
    {d r : Set P2} (hd : IsFinitePLBallPair P2 d r)
    {q : P2 → X} (hq : PolyhedralPLInCharts e q d) (hqi : InjOn q d)
    (hqR : q '' d ⊆ R) (hqS : q '' d ∩ S = q '' r) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k d ∧ InjOn k d ∧
      k '' d ⊆ interior R ∧ k '' d ∩ S = k '' r ∧
      ∃ H : C(I × d,R),
        (∀ z : d,(H (0,z) : X)=q z) ∧
        (∀ z : d,(H (1,z) : X)=k z) ∧
        ∀ (t : I) (z : d),(H (t,z) : X) ∈ S ↔ (z : P2) ∈ r := by
  classical
  let V := M.vertices → ℝ × V3
  let inv : V → X := fun z => M.inverse z
  have hinvi : InjOn inv M.complex.space := by
    intro x hx y hy hh
    exact congrArg Subtype.val (M.homeomorph.symm.injective (Subtype.ext
      ((M.inverse_eq ⟨x,hx⟩).symm.trans (hh.trans (M.inverse_eq ⟨y,hy⟩)))))
  obtain ⟨D,C,hC,hDK,hclear,G,hG0,hG1,hGval,hGfix,hGmark⟩ :=
    Dehn.exists_inward_collar_compression_homotopy M.complex M.collarBase M.finite
      M.collar_finite M.collar M.collar_pl M.collar_injective M.collar_inside M.collar_open
  have hDA : Disjoint D M.boundary.space := by
    apply disjoint_left.mpr
    intro y hyD hyA
    obtain ⟨x,hx⟩ := M.collarHomeomorph.surjective ⟨y,hyA⟩
    have hc : M.collar ((x : M.collarVertices → ℝ × V3),0)=y :=
      (M.collar_zero x).trans (congrArg Subtype.val hx)
    have hh := (hclear _ ⟨x.property,le_rfl,zero_le_one⟩).mp (hc.symm ▸ hyD)
    norm_num at hh
  have hDint : inv '' D ⊆ interior R := by
    rintro _ ⟨z,hz,rfl⟩
    have hn : inv z ∉ frontier R := fun h =>
      disjoint_left.mp hDA hz ((M.boundary_eq z (hDK hz)).mp h)
    by_contra hnot
    exact hn ⟨subset_closure (M.inverse z).property,hnot⟩
  obtain ⟨c,hc,hcv⟩ := hC
  have hcmap (z : V) (hz : z ∈ M.complex.space) : c z ∈ D :=
    hcv ⟨z,hz⟩ ▸ (C ⟨z,hz⟩).property
  have hci : InjOn c M.complex.space := by
    intro z hz w hw hh
    exact congrArg Subtype.val (C.injective (Subtype.ext
      ((hcv ⟨z,hz⟩).trans (hh.trans (hcv ⟨w,hw⟩).symm))))
  have hqM : MapsTo (M.coordinates ∘ q) d M.complex.space :=
    fun z hz => M.coordinates_mapsTo (hqR ⟨z,hz,rfl⟩)
  have hdCopy := hd
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hdCopy
  have hqcoord : FinitePiecewiseAffineOn (M.coordinates ∘ q) K.space :=
    (hKs.symm ▸ hq).finitePiecewiseAffineOn_comp K hK M.coordinates_pl
  have hcq : FinitePiecewiseAffineOn (c ∘ M.coordinates ∘ q) K.space :=
    hc.comp hqcoord (fun z hz => hqM (hKs.subset hz))
  let k : P2 → X := inv ∘ c ∘ M.coordinates ∘ q
  have hkPL : PolyhedralPLInCharts e k d := by
    rw [←hKs]
    exact M.inverse_pl.comp_finitePiecewiseAffineOn K hK hcq
      (fun z hz => hDK (hcmap _ (hqM (hKs.subset hz))))
  have hki : InjOn k d := by
    intro x hx y hy hh
    have heq := hci (hqM hx) (hqM hy)
      (hinvi (hDK (hcmap _ (hqM hx))) (hDK (hcmap _ (hqM hy))) hh)
    exact hqi hx hy (M.coordinates_injective (hqR ⟨x,hx,rfl⟩) (hqR ⟨y,hy,rfl⟩) heq)
  have hkint : k '' d ⊆ interior R := by
    rintro _ ⟨z,hz,rfl⟩
    exact hDint ⟨c (M.coordinates (q z)),hcmap _ (hqM hz),rfl⟩
  let qM : C(d,M.complex.space) := ⟨fun z => M.homeomorph ⟨q z,hqR ⟨z,z.property,rfl⟩⟩,
    M.homeomorph.continuous.comp (hq.continuousOn.domRestrict.subtype_mk _)⟩
  let H : C(I × d,R) := ⟨fun z => M.homeomorph.symm (G (z.1,qM z.2)),
    M.homeomorph.symm.continuous.comp (G.continuous.comp
      (continuous_fst.prodMk (qM.continuous.comp continuous_snd)))⟩
  have hH0 (z : d) : (H (0,z) : X)=q z := by
    change (M.homeomorph.symm (G (0,qM z)) : X)=_
    rw [hG0]
    exact congrArg Subtype.val (M.homeomorph.symm_apply_apply _)
  have hH1 (z : d) : (H (1,z) : X)=k z := by
    change (M.homeomorph.symm (G (1,qM z)) : X)=_
    rw [←M.inverse_eq,hG1,hcv]
    change (M.inverse (c (M.homeomorph ⟨q z,hqR ⟨z,z.property,rfl⟩⟩)) : X)=k z
    rw [M.homeomorph_eq]
    rfl
  have hqiff (z : d) : q z ∈ S ↔ (z : P2) ∈ r := by
    constructor
    · intro hs
      obtain ⟨w,hw,hh⟩ := hqS.subset ⟨mem_image_of_mem q z.property,hs⟩
      exact hqi (hd.1 hw) z.property hh ▸ hw
    · intro hz
      exact (hqS.symm.subset (mem_image_of_mem q hz)).2
  have hHmark (t : I) (z : d) : (H (t,z) : X) ∈ S ↔ (z : P2) ∈ r := by
    have hh := hGmark (inv ⁻¹' S)
      {x | inv (M.collar (x,0)) ∈ S} hmark t (qM z)
    change inv (G (t,qM z)) ∈ S ↔ inv (qM z) ∈ S at hh
    rw [show inv (qM z) = q z by
      change (M.inverse (M.homeomorph _) : X)=_
      rw [M.inverse_eq,M.homeomorph.symm_apply_apply]] at hh
    change (M.homeomorph.symm (G (t,qM z)) : X) ∈ S ↔ _
    rw [←M.inverse_eq]
    exact hh.trans (hqiff z)
  refine ⟨k,hkPL,hki,hkint,?_,H,hH0,hH1,hHmark⟩
  apply Subset.antisymm
  · rintro x ⟨⟨z,hz,rfl⟩,hs⟩
    exact ⟨z,(hHmark 1 ⟨z,hz⟩).mp ((hH1 ⟨z,hz⟩).symm ▸ hs),rfl⟩
  · rintro x ⟨z,hz,rfl⟩
    exact ⟨mem_image_of_mem k (hd.1 hz),
      hH1 ⟨z,hd.1 hz⟩ ▸ (hHmark 1 ⟨z,hd.1 hz⟩).mpr hz⟩

end PoincareConjecture.M76.OriginalFiniteCollarModel
