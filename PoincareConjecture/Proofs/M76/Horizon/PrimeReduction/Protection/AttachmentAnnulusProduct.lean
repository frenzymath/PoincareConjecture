import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.StandardDiskBandAnnulus
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Collars.BoundaryProductNormalization

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

theorem exists_unit_interval_annulus_coordinates :
    ∃ T : Ann ≃ₜ (Q ×ˢ I : Set (V2 × ℝ)), T.IsFinitePL ∧
      ∀ z : Ann, (T z : V2 × ℝ).2 = (depth 8 z + 1) / 2 := by
  obtain ⟨a,ha,hai,haimage,hat⟩ := exists_standard_disk_band_annulus
  let shift : (V2 × ℝ) →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      ((ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap +
        ContinuousAffineMap.const ℝ (V2 × ℝ) (1/2))
  have hs (z : V2 × ℝ) : shift z = (z.1,z.2+1/2) := rfl
  have hsi : Function.Injective shift := by
    intro x y h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    exact Prod.ext hx (by simpa only [hs,add_left_inj] using hy)
  have himage : (shift ∘ a) '' Ann = Q ×ˢ I := by
    rw [image_comp,haimage]
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      rw [hs]
      exact ⟨hw.1,by linarith [hw.2.1],by linarith [hw.2.2]⟩
    · intro hz
      refine ⟨(z.1,z.2-1/2),⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩,?_⟩
      rw [hs]
      simp
  obtain ⟨T,hT,hTval⟩ := (ha.postcomp shift).exists_homeomorph_image (hsi.injOn.comp hai (mapsTo_univ _ _))
  refine ⟨T.trans (Homeomorph.setCongr himage),hT.setCongr rfl himage,?_⟩
  intro z
  change (T z : V2 × ℝ).2 = _
  rw [hTval]
  change (shift (a z)).2 = _
  rw [hs,hat z z.property]
  ring

theorem exists_attachment_annulus_product_with_height
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : Set E} (H : Ann ≃ₜ A) (hH : H.IsFinitePL)
    (r : Bool → Set E)
    (hr : ∀ i, r i = (fun z : Ann => (H z : E)) ''
      {z | depth 8 z = if i then 1 else -1}) :
    ∃ e : A ≃ₜ (r false ×ˢ I : Set (E × ℝ)), e.IsFinitePL ∧
      (∀ i (x : A), (x : E) ∈ r i ↔
        (e x : E × ℝ) ∈ r false ×ˢ {if i then (1 : ℝ) else 0}) ∧
      ∀ x : A, (e x : E × ℝ).2 = (depth 8 (H.symm x : P2) + 1) / 2 := by
  classical
  obtain ⟨T,hT,hheight⟩ := exists_unit_interval_annulus_coordinates
  let C := T.symm.trans H
  have hC : C.IsFinitePL := hT.symm.trans hH
  have hmark (i : Bool) (x : Q ×ˢ I) :
      (C x : E) ∈ r i ↔ x.val.2 = if i then (1 : ℝ) else 0 := by
    rw [hr i]
    have hmem : (C x : E) ∈ (fun z : Ann => (H z : E)) ''
        {z | depth 8 z = if i then 1 else -1} ↔
        depth 8 (T.symm x) = if i then 1 else -1 := by
      constructor
      · rintro ⟨z,hz,hzx⟩
        have hz' : z = T.symm x := H.injective (Subtype.ext hzx)
        simpa only [hz',mem_ofPred_eq] using hz
      · intro hx
        exact ⟨T.symm x,hx,rfl⟩
    rw [hmem]
    have hh := hheight (T.symm x)
    rw [T.apply_symm_apply] at hh
    cases i <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
      constructor <;> intro h <;> linarith
  let f : Q → r false := fun x =>
    ⟨(C ⟨(x,0),x.property,by norm_num⟩ : E),(hmark false _).mpr rfl⟩
  have hf : Continuous f := by fun_prop
  have hfi : Function.Injective f := by
    intro x y h
    have hh := C.injective (Subtype.ext (congrArg (fun z : r false => (z : E)) h))
    exact Subtype.ext (congrArg (fun z : Q ×ˢ I => z.val.1) hh)
  have hfs : Function.Surjective f := by
    intro y
    have hyA : (y : E) ∈ A := by
      obtain ⟨z,_,hz⟩ := (hr false).subset y.property
      exact hz ▸ (H z).property
    let z := C.symm ⟨y,hyA⟩
    have hz : z.val.2 = 0 := (hmark false z).mp (by
      change (C (C.symm ⟨y,hyA⟩) : E) ∈ r false
      simpa only [C.apply_symm_apply] using y.property)
    refine ⟨⟨z.val.1,z.property.1⟩,Subtype.ext ?_⟩
    change (C ⟨(z.val.1,0),_⟩ : E) = y
    have heq : (⟨(z.val.1,0),by exact ⟨z.property.1,by norm_num⟩⟩ : Q ×ˢ I) = z :=
      Subtype.ext (Prod.ext rfl hz.symm)
    rw [heq]
    exact congrArg Subtype.val (C.apply_symm_apply _)
  let b := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfi,hfs⟩) hf
  obtain ⟨K,hK,hKQ⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  obtain ⟨D,hD,_,hDval,_⟩ := hC.exists_boundary_normalized_product K hK hKQ b (fun _ => rfl)
  have hcoords (x : A) : (T (H.symm x) : V2 × ℝ).2 = (D.symm x : E × ℝ).2 := by
    let z := D.symm x
    let q : Q := b.symm ⟨z.val.1,z.property.1⟩
    have hb : (b q : E) = z.val.1 := congrArg Subtype.val (b.apply_symm_apply _)
    have hv := hDval q ⟨z.val.2,z.property.2⟩
    have hz' : (⟨((b q : E),z.val.2),⟨(b q).property,z.property.2⟩⟩ : r false ×ˢ I) = z :=
      Subtype.ext (Prod.ext hb rfl)
    rw [hz'] at hv
    have hv' : x = C ⟨((q : V2),z.val.2),q.property,z.property.2⟩ := by
      apply Subtype.ext
      simpa only [z,D.apply_symm_apply] using hv
    have ht : T (H.symm x) = ⟨((q : V2),z.val.2),q.property,z.property.2⟩ := by
      apply C.injective
      simpa only [C, Homeomorph.trans_apply, T.symm_apply_apply, H.apply_symm_apply]
        using hv'
    exact congrArg (fun w : Q ×ˢ I => w.val.2) ht
  refine ⟨D.symm, hD.symm, ?_, ?_⟩
  · intro i x
    have hm := hmark i (T (H.symm x))
    simp only [C, Homeomorph.trans_apply, T.symm_apply_apply, H.apply_symm_apply] at hm
    rw [hcoords] at hm
    exact hm.trans (and_iff_right (D.symm x).property.1).symm
  · intro x
    exact (hcoords x).symm.trans (hheight (H.symm x))

theorem exists_attachment_annulus_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : Set E} (H : Ann ≃ₜ A) (hH : H.IsFinitePL)
    (r : Bool → Set E)
    (hr : ∀ i, r i = (fun z : Ann => (H z : E)) ''
      {z | depth 8 z = if i then 1 else -1}) :
    ∃ e : A ≃ₜ (r false ×ˢ I : Set (E × ℝ)), e.IsFinitePL ∧
      ∀ i (x : A), (x : E) ∈ r i ↔
        (e x : E × ℝ) ∈ r false ×ˢ {if i then (1 : ℝ) else 0} := by
  obtain ⟨e, he, hmark, _⟩ := exists_attachment_annulus_product_with_height H hH r hr
  exact ⟨e, he, hmark⟩

end PoincareConjecture.M76
