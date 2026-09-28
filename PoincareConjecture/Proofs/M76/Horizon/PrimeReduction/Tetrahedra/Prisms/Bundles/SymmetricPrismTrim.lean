import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberReflection



set_option autoImplicit false
noncomputable section
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

def trimInterval (t : I) : I :=
  ⟨1/4+(t : ℝ)/2,by constructor <;> nlinarith [t.property.1,t.property.2]⟩

theorem trimInterval_mem (t : I) : (trimInterval t : ℝ) ∈ Icc (1/4 : ℝ) (3/4) := by
  change 1/4+(t : ℝ)/2 ∈ _
  constructor <;> nlinarith [t.property.1,t.property.2]

theorem trimInterval_injective : Function.Injective trimInterval := by
  intro s t h
  apply Subtype.ext
  have he := congrArg (fun t : I => (t : ℝ)) h
  change 1/4+(s : ℝ)/2 = 1/4+(t : ℝ)/2 at he
  linarith

theorem trimInterval_flip (b : Bool) (t : I) :
    trimInterval (fiberFlip b t) = fiberFlip b (trimInterval t) := by
  apply Subtype.ext
  cases b
  · rfl
  · change 1/4+(1-(t : ℝ))/2 = 1-(1/4+(t : ℝ)/2)
    ring

theorem fiberFlip_mem_middle_iff (b : Bool) (t : I) :
    (fiberFlip b t : ℝ) ∈ Icc (1/4 : ℝ) (3/4) ↔ (t : ℝ) ∈ Icc (1/4 : ℝ) (3/4) := by
  cases b
  · rfl
  · change (1-(t : ℝ) ∈ Icc (1/4 : ℝ) (3/4)) ↔ _
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

def trimProduct {E : Type*} (A : Set E) (x : (A ×ˢ I : Set (E × ℝ))) :
    (A ×ˢ I : Set (E × ℝ)) :=
  ⟨((x : E × ℝ).1,trimInterval ⟨(x : E × ℝ).2,x.property.2⟩),x.property.1,(trimInterval _).property⟩

def prismTrim {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) : Set F :=
  range (fun x => (H (trimProduct A x) : F))

theorem prismTrim_subset {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) : prismTrim H ⊆ B := by
  rintro _ ⟨x,rfl⟩
  exact (H _).property

theorem mem_prismTrim_iff {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    (x : F) ∈ prismTrim H ↔ (H.symm x : E × ℝ).2 ∈ Icc (1/4 : ℝ) (3/4) := by
  constructor
  · rintro ⟨y,hy⟩
    have he : H (trimProduct A y) = x := Subtype.ext hy
    rw [←he,H.symm_apply_apply]
    exact trimInterval_mem ⟨(y : E × ℝ).2,y.property.2⟩
  · intro hx
    let z := H.symm x
    let t : I := ⟨2*(z : E × ℝ).2-1/2,by constructor <;> dsimp [z] <;> linarith [hx.1,hx.2]⟩
    let y : (A ×ˢ I : Set (E × ℝ)) := ⟨((z : E × ℝ).1,t),z.property.1,t.property⟩
    have hy : trimProduct A y = z := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change 1/4+(2*(z : E × ℝ).2-1/2)/2 = (z : E × ℝ).2
        ring
    exact ⟨y,congrArg Subtype.val ((congrArg H hy).trans (H.apply_symm_apply x))⟩

theorem prismTrim_disjoint_caps
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B B₀ B₁ : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (h₀ : ∀ x, (H x : F) ∈ B₀ ↔ (x : E × ℝ).2 = 0)
    (h₁ : ∀ x, (H x : F) ∈ B₁ ↔ (x : E × ℝ).2 = 1) :
    Disjoint (prismTrim H) (B₀ ∪ B₁) := by
  apply disjoint_left.mpr
  rintro x ⟨y,rfl⟩ (hx | hx)
  · have hh := (h₀ _).mp hx
    have hm := trimInterval_mem ⟨(y : E × ℝ).2,y.property.2⟩
    change (trimInterval _ : ℝ) = 0 at hh
    linarith [hm.1]
  · have hh := (h₁ _).mp hx
    have hm := trimInterval_mem ⟨(y : E × ℝ).2,y.property.2⟩
    change (trimInterval _ : ℝ) = 1 at hh
    linarith [hm.2]

theorem exists_finitePL_symmetric_prism_trim
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : Set E} {B : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (hH : H.IsFinitePL) :
    ∃ C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H, C.IsFinitePL ∧
      ∀ x, (C x : F) = H (trimProduct A x) := by
  obtain ⟨f,hf,hfval⟩ := hH
  obtain ⟨K,hK,hKs,hKf⟩ := hf
  let q : (E × ℝ) →ᴬ[ℝ] (E × ℝ) :=
    ((ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap).prod
      (ContinuousAffineMap.const ℝ (E × ℝ) (1/4 : ℝ) +
        (1/2 : ℝ) • (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hq (x : (A ×ˢ I : Set (E × ℝ))) : q x = (trimProduct A x : E × ℝ) := by
    apply Prod.ext
    · rfl
    · change 1/4+(1/2)* (x : E × ℝ).2 = 1/4+(x : E × ℝ).2/2
      ring
  have hqmap : MapsTo q (A ×ˢ I) (A ×ˢ I) := by
    intro x hx
    rw [hq ⟨x,hx⟩]
    exact (trimProduct A ⟨x,hx⟩).property
  have hqPL : FinitePiecewiseAffineOn q (A ×ˢ I) :=
    ⟨K,hK,hKs,K.affineOnFaces_affine q⟩
  have hcomp : FinitePiecewiseAffineOn (f ∘ q) (A ×ˢ I) :=
    (show FinitePiecewiseAffineOn f (A ×ˢ I) from ⟨K,hK,hKs,hKf⟩).comp hqPL hqmap
  have hval (x : (A ×ˢ I : Set (E × ℝ))) : (f ∘ q) x = (H (trimProduct A x) : F) := by
    rw [Function.comp_apply,hq,←hfval]
  have hinj : InjOn (f ∘ q) (A ×ˢ I) := by
    intro x hx y hy he
    have ht := H.injective (Subtype.ext ((hval ⟨x,hx⟩).symm.trans (he.trans (hval ⟨y,hy⟩))))
    have hp := congrArg (fun x : (A ×ˢ I : Set (E × ℝ)) => (x : E × ℝ)) ht
    apply Prod.ext
    · have hh := congrArg (fun z : E × ℝ => z.1) hp
      exact hh
    · have hh := congrArg Prod.snd hp
      change 1/4+x.2/2 = 1/4+y.2/2 at hh
      linarith
  have himage : (f ∘ q) '' (A ×ˢ I) = prismTrim H := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,(hval _).symm⟩
    · rintro ⟨x,rfl⟩
      exact ⟨x,x.property,hval x⟩
  have hex := hcomp.exists_homeomorph_image hinj
  rw [himage] at hex
  obtain ⟨C,hC,hCv⟩ := hex
  exact ⟨C,hC,fun x => (hCv x).trans (hval x)⟩

end PoincareConjecture.M76.PrismBelt
