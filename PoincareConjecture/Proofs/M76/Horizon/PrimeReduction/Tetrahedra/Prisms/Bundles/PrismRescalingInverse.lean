import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.QuarterPrismRescaling

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem inverse_quarter_height (δ t : ℝ) (hhalf : δ < 1/2) :
    affineFiberHeight ((1/4-δ)/(1-2*δ)) (δ+(1-2*δ)*t) = 1/4+t/2 := by
  have hc : 1-2*δ ≠ 0 := by linarith
  unfold affineFiberHeight
  field_simp [hc,show 1-δ*2 ≠ 0 by linarith]
  <;> ring

theorem quarter_prism_inverse_admissible
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ < 1/2)
    (Cδ : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrimAt H δ)
    (hCδ : ∀ x, (Cδ x : E) = H (prismScaleProduct A δ hδ hhalf x))
    (x : prismTrimAt H δ) :
    affineFiberHeight ((1/4-δ)/(1-2*δ))
      (H.symm ⟨x,prismTrimAt_subset H δ x.property⟩ : E × ℝ).2 ∈ I := by
  let y := Cδ.symm x
  have hx : (x : E) = H (prismScaleProduct A δ hδ hhalf y) := by
    simpa only [y,Cδ.apply_symm_apply] using hCδ y
  have hsource : H.symm ⟨x,prismTrimAt_subset H δ x.property⟩ = prismScaleProduct A δ hδ hhalf y := by
    apply H.injective
    exact (H.apply_symm_apply _).trans (Subtype.ext hx)
  rw [hsource]
  change affineFiberHeight ((1/4-δ)/(1-2*δ)) (δ+(1-2*δ)*(y : E × ℝ).2) ∈ I
  rw [inverse_quarter_height δ _ hhalf]
  constructor <;> linarith [y.property.2.1,y.property.2.2]

theorem quarter_prism_inverse_eq_affine
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H)
    (hCv : ∀ x, (C x : E) = H (trimProduct A x))
    (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ < 1/2)
    (Cδ : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrimAt H δ)
    (hCδ : ∀ x, (Cδ x : E) = H (prismScaleProduct A δ hδ hhalf x))
    (x : prismTrimAt H δ) :
    (C (Cδ.symm x) : E) =
      prismAffineFiberPoint H ⟨x,prismTrimAt_subset H δ x.property⟩ ((1/4-δ)/(1-2*δ))
        (quarter_prism_inverse_admissible H δ hδ hhalf Cδ hCδ x) := by
  let y := Cδ.symm x
  have hx : (x : E) = H (prismScaleProduct A δ hδ hhalf y) := by
    simpa only [y,Cδ.apply_symm_apply] using hCδ y
  have hsource : H.symm ⟨x,prismTrimAt_subset H δ x.property⟩ = prismScaleProduct A δ hδ hhalf y := by
    apply H.injective
    exact (H.apply_symm_apply _).trans (Subtype.ext hx)
  rw [hCv]
  change (H (trimProduct A y) : E) = H _
  congr 2
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun z : (A ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).1) hsource).symm
  · change 1/4+(y : E × ℝ).2/2 = affineFiberHeight ((1/4-δ)/(1-2*δ))
      (H.symm ⟨x,prismTrimAt_subset H δ x.property⟩ : E × ℝ).2
    rw [hsource]
    exact (inverse_quarter_height δ (y : E × ℝ).2 hhalf).symm

end PoincareConjecture.M76.PrismBelt
