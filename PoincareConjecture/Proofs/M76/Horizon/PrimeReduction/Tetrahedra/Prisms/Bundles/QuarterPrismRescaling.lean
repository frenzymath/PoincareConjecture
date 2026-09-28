import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.VariableSymmetricPrismTrim
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismAffineFiberParameter



set_option autoImplicit false
noncomputable section
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

def prismScaleProduct {E : Type*} (A : Set E) (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ < 1/2)
    (x : (A ×ˢ I : Set (E × ℝ))) : (A ×ˢ I : Set (E × ℝ)) :=
  ⟨((x : E × ℝ).1,δ+(1-2*δ)*(x : E × ℝ).2),x.property.1,by
    have hc : 0 ≤ 1-2*δ := by linarith
    constructor
    · nlinarith [mul_nonneg hc x.property.2.1]
    · nlinarith [mul_nonneg hc (sub_nonneg.mpr x.property.2.2)]⟩

theorem prismTrimAt_zero
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F] {A : Set E} {B : Set F}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) : prismTrimAt H 0 = B := by
  apply Subset.antisymm (prismTrimAt_subset H 0)
  intro x hx
  exact ⟨hx,by simpa only [sub_zero] using (H.symm ⟨x,hx⟩).property.2⟩

theorem exists_finitePL_prism_scale_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : Set E} {B : Set F} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (hH : H.IsFinitePL)
    (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ < 1/2) :
    ∃ C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrimAt H δ, C.IsFinitePL ∧
      ∀ x, (C x : F) = H (prismScaleProduct A δ hδ hhalf x) := by
  by_cases hz : δ = 0
  · subst δ
    let C := H.trans (Homeomorph.setCongr (prismTrimAt_zero H).symm)
    refine ⟨C,?_,?_⟩
    · obtain ⟨f,hf,hfv⟩ := hH
      exact ⟨f,hf,hfv⟩
    · intro x
      change (H x : F) = H (prismScaleProduct A 0 hδ hhalf x)
      congr 2
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · simp [prismScaleProduct]
  · exact exists_finitePL_prism_trim_at H hH δ (lt_of_le_of_ne hδ (Ne.symm hz)) hhalf

theorem quarter_prism_scale_admissible
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H)
    (hCv : ∀ x, (C x : E) = H (trimProduct A x))
    (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ < 1/2) (x : prismTrim H) :
    affineFiberHeight (2*δ-1/2)
      (H.symm ⟨x,prismTrim_subset H x.property⟩ : E × ℝ).2 ∈ I := by
  let y := C.symm x
  have hx : (x : E) = H (trimProduct A y) := by
    simpa only [y,C.apply_symm_apply] using hCv y
  have hsource : H.symm ⟨x,prismTrim_subset H x.property⟩ = trimProduct A y := by
    apply H.injective
    exact (H.apply_symm_apply _).trans (Subtype.ext hx)
  have he : affineFiberHeight (2*δ-1/2)
      (H.symm ⟨x,prismTrim_subset H x.property⟩ : E × ℝ).2 =
      (prismScaleProduct A δ hδ hhalf y : E × ℝ).2 := by
    rw [hsource]
    change (1-(2*δ-1/2))*(1/4+(y : E × ℝ).2/2)+
      (2*δ-1/2)*(1-(1/4+(y : E × ℝ).2/2)) = δ+(1-2*δ)*(y : E × ℝ).2
    ring
  rw [he]
  exact (prismScaleProduct A δ hδ hhalf y).property.2

theorem quarter_prism_scale_eq_affine
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H)
    (hCv : ∀ x, (C x : E) = H (trimProduct A x))
    (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ < 1/2) (x : prismTrim H) :
    (H (prismScaleProduct A δ hδ hhalf (C.symm x)) : E) =
      prismAffineFiberPoint H ⟨x,prismTrim_subset H x.property⟩ (2*δ-1/2)
        (quarter_prism_scale_admissible H C hCv δ hδ hhalf x) := by
  let y := C.symm x
  have hx : (x : E) = H (trimProduct A y) := by
    simpa only [y,C.apply_symm_apply] using hCv y
  have hsource : H.symm ⟨x,prismTrim_subset H x.property⟩ = trimProduct A y := by
    apply H.injective
    exact (H.apply_symm_apply _).trans (Subtype.ext hx)
  change (H _ : E) = H _
  congr 2
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun z : (A ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).1) hsource).symm
  · change δ+(1-2*δ)*(y : E × ℝ).2 = affineFiberHeight (2*δ-1/2)
      (H.symm ⟨x,prismTrim_subset H x.property⟩ : E × ℝ).2
    rw [hsource]
    change δ+(1-2*δ)*(y : E × ℝ).2 =
      (1-(2*δ-1/2))*(1/4+(y : E × ℝ).2/2)+
        (2*δ-1/2)*(1-(1/4+(y : E × ℝ).2/2))
    ring

end PoincareConjecture.M76.PrismBelt
