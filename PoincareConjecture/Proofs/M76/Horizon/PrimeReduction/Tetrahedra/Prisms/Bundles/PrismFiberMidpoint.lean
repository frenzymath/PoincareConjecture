import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.AffineEdgeFiberReflection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.TrimmedFiberReflection

set_option autoImplicit false
noncomputable section
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

def fiberMidHeight : I := ⟨1/2,by norm_num⟩

@[simp] theorem fiberFlip_midHeight (b : Bool) : fiberFlip b fiberMidHeight = fiberMidHeight := by
  apply Subtype.ext
  cases b
  · rfl
  · change 1-(1/2 : ℝ) = 1/2
    norm_num

def prismFiberMidpoint {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) : B :=
  H ⟨((H.symm x : E × ℝ).1,fiberMidHeight),(H.symm x).property.1,fiberMidHeight.property⟩

theorem continuous_prismFiberMidpoint {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) : Continuous (prismFiberMidpoint H) := by
  unfold prismFiberMidpoint
  fun_prop

theorem prismFiberMidpoint_idempotent {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    prismFiberMidpoint H (prismFiberMidpoint H x) = prismFiberMidpoint H x := by
  simp only [prismFiberMidpoint,H.symm_apply_apply]

theorem prismFiberMidpoint_reflection {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    prismFiberMidpoint H (prismFiberReflection H x) = prismFiberMidpoint H x := by
  simp only [prismFiberMidpoint,prismFiberReflection,Homeomorph.trans_apply,H.symm_apply_apply]
  rfl

theorem prismFiberMidpoint_fixed {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    prismFiberReflection H (prismFiberMidpoint H x) = prismFiberMidpoint H x := by
  apply (prismFiberReflection_eq_iff_height H _).mpr
  simp only [prismFiberMidpoint,H.symm_apply_apply]
  rfl

theorem prismFiberMidpoint_eq_self_iff {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    prismFiberMidpoint H x = x ↔ prismFiberReflection H x = x := by
  rw [prismFiberReflection_eq_iff_height]
  constructor
  · intro h
    have hh := congrArg (fun y : B => (H.symm y : E × ℝ).2) h
    simpa only [prismFiberMidpoint,H.symm_apply_apply,fiberMidHeight] using hh.symm
  · intro hh
    apply H.symm.injective
    simp only [prismFiberMidpoint,H.symm_apply_apply]
    apply Subtype.ext
    exact Prod.ext rfl hh.symm

theorem prismFiberMidpoint_on_global_rectangle
    {E : Type*} [TopologicalSpace E] {A B M : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (u t : I) :
    (prismFiberMidpoint H ⟨G ⟨(u,t),u.property,t.property⟩,hMB (G _).property⟩ : E) =
      G ⟨(u,fiberMidHeight),u.property,fiberMidHeight.property⟩ := by
  have h0 := prism_inverse_on_global_rectangle H G hMB flip hformula u t
  have h1 := prism_inverse_on_global_rectangle H G hMB flip hformula u fiberMidHeight
  apply congrArg (fun x : B => (x : E)) (a₂ :=
    ⟨G ⟨(u,fiberMidHeight),u.property,fiberMidHeight.property⟩,hMB (G _).property⟩)
  apply H.symm.injective
  apply Subtype.ext
  simp only [prismFiberMidpoint,H.symm_apply_apply,h0,h1,fiberFlip_midHeight]

theorem prismFiberMidpoint_on_affine_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B M : Set E} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip b : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (hside : ∀ t, (G (sidePoint b t) : E) =
      AffineMap.lineMap (G (sidePoint b 0) : E) (G (sidePoint b 1) : E) (t : ℝ))
    (t : I) :
    (prismFiberMidpoint H ⟨G (sidePoint b t),hMB (G _).property⟩ : E) =
      (1/2 : ℝ) • ((G (sidePoint b t) : E) +
        prismFiberReflection H ⟨G (sidePoint b t),hMB (G _).property⟩) := by
  have hmid : (prismFiberMidpoint H ⟨G (sidePoint b t),hMB (G _).property⟩ : E) =
      G (sidePoint b fiberMidHeight) := by
    cases b
    · exact prismFiberMidpoint_on_global_rectangle H G hMB flip hformula 0 t
    · exact prismFiberMidpoint_on_global_rectangle H G hMB flip hformula 1 t
  rw [hmid,hside fiberMidHeight,
    prismFiberReflection_on_affine_side H G hMB flip b hformula hside t]
  change AffineMap.lineMap _ _ (1/2 : ℝ) = _
  simp only [AffineMap.lineMap_apply_module]
  module

theorem prismFiberMidpoint_trim_chart
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H)
    (hC : ∀ x, (C x : E) = H (trimProduct A x)) (x : prismTrim H) :
    (prismFiberMidpoint C x : E) =
      prismFiberMidpoint H ⟨x,prismTrim_subset H x.property⟩ := by
  let y := C.symm x
  have hx : (x : E) = H (trimProduct A y) := by
    simpa only [y,C.apply_symm_apply] using hC y
  have hsource : H.symm ⟨x,prismTrim_subset H x.property⟩ = trimProduct A y := by
    apply H.injective
    exact (H.apply_symm_apply _).trans (Subtype.ext hx)
  change (C ⟨((y : E × ℝ).1,fiberMidHeight),y.property.1,fiberMidHeight.property⟩ : E) = _
  rw [hC]
  unfold prismFiberMidpoint
  apply congrArg (fun z => (H z : E))
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun z : (A ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).1) hsource).symm
  · change 1/4+(1/2 : ℝ)/2 = 1/2
    norm_num

end PoincareConjecture.M76.PrismBelt
