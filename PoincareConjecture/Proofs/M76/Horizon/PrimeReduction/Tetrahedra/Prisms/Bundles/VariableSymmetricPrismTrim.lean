import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.SymmetricPrismTrim
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberMidpoint

set_option autoImplicit false
noncomputable section
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

def trimIntervalAt (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2) (t : I) : I :=
  ⟨δ+(1-2*δ)*(t : ℝ),by
    have hc : 0 < 1-2*δ := by linarith
    constructor
    · nlinarith [mul_nonneg (le_of_lt hc) t.property.1]
    · nlinarith [mul_nonneg (le_of_lt hc) (sub_nonneg.mpr t.property.2)]⟩

theorem trimIntervalAt_mem (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2) (t : I) :
    (trimIntervalAt δ hδ hhalf t : ℝ) ∈ Icc δ (1-δ) := by
  have hc : 0 ≤ 1-2*δ := by linarith
  change δ+(1-2*δ)*(t : ℝ) ∈ _
  constructor
  · nlinarith [mul_nonneg hc t.property.1]
  · nlinarith [mul_nonneg hc (sub_nonneg.mpr t.property.2)]

theorem trimIntervalAt_flip (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2) (b : Bool) (t : I) :
    trimIntervalAt δ hδ hhalf (fiberFlip b t) = fiberFlip b (trimIntervalAt δ hδ hhalf t) := by
  apply Subtype.ext
  cases b
  · rfl
  · change δ+(1-2*δ)*(1-(t : ℝ)) = 1-(δ+(1-2*δ)*(t : ℝ))
    ring

def trimProductAt {E : Type*} (A : Set E) (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (x : (A ×ˢ I : Set (E × ℝ))) : (A ×ˢ I : Set (E × ℝ)) :=
  ⟨((x : E × ℝ).1,trimIntervalAt δ hδ hhalf ⟨(x : E × ℝ).2,x.property.2⟩),
    x.property.1,(trimIntervalAt δ hδ hhalf _).property⟩

def prismTrimAt {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (δ : ℝ) : Set F :=
  {y | ∃ hy : y ∈ B, (H.symm ⟨y,hy⟩ : E × ℝ).2 ∈ Icc δ (1-δ)}

theorem prismTrimAt_subset {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (δ : ℝ) :
    prismTrimAt H δ ⊆ B := fun _ hx => hx.choose

theorem mem_prismTrimAt_iff {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (δ : ℝ) (x : B) :
    (x : F) ∈ prismTrimAt H δ ↔ (H.symm x : E × ℝ).2 ∈ Icc δ (1-δ) :=
  ⟨fun hx => hx.choose_spec,fun hx => ⟨x.property,hx⟩⟩

theorem prismTrimAt_range {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2) :
    prismTrimAt H δ = range (fun x => (H (trimProductAt A δ hδ hhalf x) : F)) := by
  have hc : 0 < 1-2*δ := by linarith
  ext y
  constructor
  · rintro ⟨hy,hheight⟩
    let z := H.symm ⟨y,hy⟩
    let t : I := ⟨((z : E × ℝ).2-δ)/(1-2*δ),by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hheight.1) (le_of_lt hc)
      · apply (div_le_one hc).mpr
        dsimp [z]
        linarith [hheight.2]⟩
    let x : (A ×ˢ I : Set (E × ℝ)) := ⟨((z : E × ℝ).1,t),z.property.1,t.property⟩
    have hx : trimProductAt A δ hδ hhalf x = z := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change δ+(1-2*δ)*(((z : E × ℝ).2-δ)/(1-2*δ)) = (z : E × ℝ).2
        rw [mul_div_cancel₀ _ hc.ne']
        ring
    refine ⟨x,?_⟩
    change (H (trimProductAt A δ hδ hhalf x) : F) = y
    rw [hx]
    exact congrArg Subtype.val (H.apply_symm_apply ⟨y,hy⟩)
  · rintro ⟨x,rfl⟩
    refine ⟨(H _).property,?_⟩
    change (H.symm (H _) : E × ℝ).2 ∈ _
    rw [H.symm_apply_apply]
    exact trimIntervalAt_mem δ hδ hhalf ⟨(x : E × ℝ).2,x.property.2⟩

theorem exists_finitePL_prism_trim_at
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : Set E} {B : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (hH : H.IsFinitePL)
    (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2) :
    ∃ C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrimAt H δ, C.IsFinitePL ∧
      ∀ x, (C x : F) = H (trimProductAt A δ hδ hhalf x) := by
  obtain ⟨f,hf,hfval⟩ := hH
  obtain ⟨K,hK,hKs,hKf⟩ := hf
  let q : (E × ℝ) →ᴬ[ℝ] (E × ℝ) :=
    ((ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap).prod
      (ContinuousAffineMap.const ℝ (E × ℝ) δ +
        (1-2*δ) • (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hq (x : (A ×ˢ I : Set (E × ℝ))) : q x = (trimProductAt A δ hδ hhalf x : E × ℝ) := rfl
  have hqmap : MapsTo q (A ×ˢ I) (A ×ˢ I) := by
    intro x hx
    rw [hq ⟨x,hx⟩]
    exact (trimProductAt A δ hδ hhalf ⟨x,hx⟩).property
  have hqPL : FinitePiecewiseAffineOn q (A ×ˢ I) :=
    ⟨K,hK,hKs,K.affineOnFaces_affine q⟩
  have hcomp : FinitePiecewiseAffineOn (f ∘ q) (A ×ˢ I) :=
    (show FinitePiecewiseAffineOn f (A ×ˢ I) from ⟨K,hK,hKs,hKf⟩).comp hqPL hqmap
  have hval (x : (A ×ˢ I : Set (E × ℝ))) :
      (f ∘ q) x = (H (trimProductAt A δ hδ hhalf x) : F) := by
    rw [Function.comp_apply,hq,←hfval]
  have hinj : InjOn (f ∘ q) (A ×ˢ I) := by
    intro x hx y hy he
    have ht := H.injective (Subtype.ext ((hval ⟨x,hx⟩).symm.trans (he.trans (hval ⟨y,hy⟩))))
    have hp := congrArg (fun x : (A ×ˢ I : Set (E × ℝ)) => (x : E × ℝ)) ht
    apply Prod.ext
    · have hh := congrArg Prod.fst hp
      exact hh
    · have hh := congrArg Prod.snd hp
      change δ+(1-2*δ)*x.2 = δ+(1-2*δ)*y.2 at hh
      have hc : 0 < 1-2*δ := by linarith
      nlinarith
  have himage : (f ∘ q) '' (A ×ˢ I) = prismTrimAt H δ := by
    rw [prismTrimAt_range H δ hδ hhalf]
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

theorem trimProductAt_reflection {E : Type*} [TopologicalSpace E] (A : Set E)
    (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2) (x : (A ×ˢ I : Set (E × ℝ))) :
    trimProductAt A δ hδ hhalf (productFiberReflection A x) =
      productFiberReflection A (trimProductAt A δ hδ hhalf x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change δ+(1-2*δ)*(1-(x : E × ℝ).2) = 1-(δ+(1-2*δ)*(x : E × ℝ).2)
    ring

theorem prismFiberReflection_trimAt_chart
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrimAt H δ)
    (hC : ∀ x, (C x : E) = H (trimProductAt A δ hδ hhalf x)) (x : prismTrimAt H δ) :
    (prismFiberReflection C x : E) =
      prismFiberReflection H ⟨x,prismTrimAt_subset H δ x.property⟩ := by
  let y := C.symm x
  have hx : (x : E) = H (trimProductAt A δ hδ hhalf y) := by
    simpa only [y,C.apply_symm_apply] using hC y
  have hsource : H.symm ⟨x,prismTrimAt_subset H δ x.property⟩ = trimProductAt A δ hδ hhalf y := by
    apply H.injective
    exact (H.apply_symm_apply _).trans (Subtype.ext hx)
  change (C (productFiberReflection A y) : E) =
    H (productFiberReflection A (H.symm ⟨x,prismTrimAt_subset H δ x.property⟩))
  rw [hC,trimProductAt_reflection,hsource]

theorem prismFiberMidpoint_mem_trimAt
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (δ : ℝ) (hhalf : δ < 1/2) (x : B) :
    (prismFiberMidpoint H x : E) ∈ prismTrimAt H δ := by
  apply (mem_prismTrimAt_iff H δ _).mpr
  simp only [prismFiberMidpoint,H.symm_apply_apply]
  change (1/2 : ℝ) ∈ Icc δ (1-δ)
  constructor <;> linarith

theorem prismTrimAt_disjoint_caps
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B B₀ B₁ : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (h₀ : ∀ x, (H x : F) ∈ B₀ ↔ (x : E × ℝ).2 = 0)
    (h₁ : ∀ x, (H x : F) ∈ B₁ ↔ (x : E × ℝ).2 = 1)
    (δ : ℝ) (hδ : 0 < δ) : Disjoint (prismTrimAt H δ) (B₀ ∪ B₁) := by
  apply disjoint_left.mpr
  rintro x ⟨hx,hheight⟩ (hcap | hcap)
  · have hh := (h₀ (H.symm ⟨x,hx⟩)).mp
      (by simpa only [H.apply_symm_apply] using hcap)
    linarith [hheight.1]
  · have hh := (h₁ (H.symm ⟨x,hx⟩)).mp
      (by simpa only [H.apply_symm_apply] using hcap)
    linarith [hheight.2]

end PoincareConjecture.M76.PrismBelt
