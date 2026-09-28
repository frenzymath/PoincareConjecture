import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberEndpointPairs

set_option autoImplicit false
noncomputable section
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

def fiberInterpolation (s t : I) : I :=
  ⟨(1-(t : ℝ))*(s : ℝ)+(t : ℝ)*(1-(s : ℝ)),by
    obtain ⟨hs0,hs1⟩ := s.property
    obtain ⟨ht0,ht1⟩ := t.property
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hs0)
        (mul_nonneg ht0 (sub_nonneg.mpr hs1))
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hs1),mul_nonneg ht0 hs0]⟩

theorem continuous_fiberInterpolation : Continuous (fun z : I × I => fiberInterpolation z.1 z.2) := by
  unfold fiberInterpolation
  fun_prop

@[simp] theorem fiberInterpolation_zero (s : I) : fiberInterpolation s 0 = s := by
  apply Subtype.ext
  simp [fiberInterpolation]

@[simp] theorem fiberInterpolation_one (s : I) : fiberInterpolation s 1 = unitInterval.symm s := by
  apply Subtype.ext
  simp [fiberInterpolation,unitInterval.symm]

@[simp] theorem fiberInterpolation_from_zero (t : I) : fiberInterpolation 0 t = t := by
  apply Subtype.ext
  simp [fiberInterpolation]

@[simp] theorem fiberInterpolation_from_one (t : I) : fiberInterpolation 1 t = unitInterval.symm t := by
  apply Subtype.ext
  simp [fiberInterpolation,unitInterval.symm]

theorem fiberInterpolation_flip (b : Bool) (s t : I) :
    fiberFlip b (fiberInterpolation (fiberFlip b s) t) = fiberInterpolation s t := by
  cases b
  · rfl
  · apply Subtype.ext
    change 1-((1-(t : ℝ))*(1-(s : ℝ))+(t : ℝ)*(1-(1-(s : ℝ)))) =
      (1-(t : ℝ))*(s : ℝ)+(t : ℝ)*(1-(s : ℝ))
    ring

theorem fiberInterpolation_trim (s t : I) :
    trimInterval (fiberInterpolation s t) = fiberInterpolation (trimInterval s) t := by
  apply Subtype.ext
  change 1/4+((1-(t : ℝ))*(s : ℝ)+(t : ℝ)*(1-(s : ℝ)))/2 =
    (1-(t : ℝ))*(1/4+(s : ℝ)/2)+(t : ℝ)*(1-(1/4+(s : ℝ)/2))
  ring

def prismFiberInterpolation {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) (t : I) : B :=
  prismFiberPoint H x (fiberInterpolation ⟨(H.symm x : E × ℝ).2,(H.symm x).property.2⟩ t)

theorem continuous_prismFiberInterpolation {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) :
    Continuous (fun z : B × I => prismFiberInterpolation H z.1 z.2) := by
  unfold prismFiberInterpolation prismFiberPoint fiberInterpolation
  fun_prop

@[simp] theorem prismFiberInterpolation_zero {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    prismFiberInterpolation H x 0 = x := by
  simp only [prismFiberInterpolation,fiberInterpolation_zero,prismFiberPoint]
  exact H.apply_symm_apply x

theorem prismFiberInterpolation_on_global_rectangle
    {E : Type*} [TopologicalSpace E] {A B M : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (u s t : I) :
    (prismFiberInterpolation H ⟨G ⟨(u,s),u.property,s.property⟩,hMB (G _).property⟩ t : E) =
      G ⟨(u,fiberInterpolation s t),u.property,(fiberInterpolation s t).property⟩ := by
  have h0 := prism_inverse_on_global_rectangle H G hMB flip hformula u s
  have hs : (⟨(H.symm ⟨G ⟨(u,s),u.property,s.property⟩,hMB (G _).property⟩ : E × ℝ).2,
      (H.symm _).property.2⟩ : I) = fiberFlip flip s := Subtype.ext (congrArg Prod.snd h0)
  rw [prismFiberInterpolation,hs,prismFiberPoint_on_global_rectangle H G hMB flip hformula,
    fiberInterpolation_flip]

theorem prismFiberInterpolation_on_affine_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B M : Set E} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip b : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (hside : ∀ t, (G (sidePoint b t) : E) =
      AffineMap.lineMap (G (sidePoint b 0) : E) (G (sidePoint b 1) : E) (t : ℝ))
    (s t : I) :
    (prismFiberInterpolation H ⟨G (sidePoint b s),hMB (G _).property⟩ t : E) =
      AffineMap.lineMap (G (sidePoint b s) : E)
        (prismFiberReflection H ⟨G (sidePoint b s),hMB (G _).property⟩ : E) (t : ℝ) := by
  have hi : (prismFiberInterpolation H ⟨G (sidePoint b s),hMB (G _).property⟩ t : E) =
      G (sidePoint b (fiberInterpolation s t)) := by
    cases b
    · exact prismFiberInterpolation_on_global_rectangle H G hMB flip hformula 0 s t
    · exact prismFiberInterpolation_on_global_rectangle H G hMB flip hformula 1 s t
  rw [hi,prismFiberReflection_on_affine_side H G hMB flip b hformula hside s,
    hside (fiberInterpolation s t),hside s]
  simp only [AffineMap.lineMap_apply_module,fiberInterpolation]
  module

theorem prismFiberInterpolation_trim_chart
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H)
    (hC : ∀ x, (C x : E) = H (trimProduct A x)) (x : prismTrim H) (t : I) :
    (prismFiberInterpolation C x t : E) =
      prismFiberInterpolation H ⟨x,prismTrim_subset H x.property⟩ t := by
  let y := C.symm x
  have hx : (x : E) = H (trimProduct A y) := by
    simpa only [y,C.apply_symm_apply] using hC y
  have hsource : H.symm ⟨x,prismTrim_subset H x.property⟩ = trimProduct A y := by
    apply H.injective
    exact (H.apply_symm_apply _).trans (Subtype.ext hx)
  have hheight : (⟨(H.symm ⟨x,prismTrim_subset H x.property⟩ : E × ℝ).2,
      (H.symm _).property.2⟩ : I) = trimInterval ⟨(y : E × ℝ).2,y.property.2⟩ := by
    apply Subtype.ext
    exact congrArg (fun z : (A ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).2) hsource
  rw [prismFiberInterpolation,prismFiberPoint_trim_chart H C hC,prismFiberInterpolation,
    hheight,←fiberInterpolation_trim]

end PoincareConjecture.M76.PrismBelt
