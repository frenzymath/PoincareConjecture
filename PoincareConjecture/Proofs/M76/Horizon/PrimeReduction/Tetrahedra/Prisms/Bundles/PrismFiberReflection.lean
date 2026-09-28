import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalSharedFaceFibers



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

def productFiberReflection {E : Type*} [TopologicalSpace E] (A : Set E) :
    (A ×ˢ I : Set (E × ℝ)) ≃ₜ (A ×ˢ I : Set (E × ℝ)) :=
  (Homeomorph.Set.prod A I).trans
    (((Homeomorph.refl A).prodCongr unitInterval.symmHomeomorph).trans
      (Homeomorph.Set.prod A I).symm)

theorem productFiberReflection_value {E : Type*} [TopologicalSpace E] (A : Set E)
    (x : (A ×ˢ I : Set (E × ℝ))) :
    (productFiberReflection A x : E × ℝ) = ((x : E × ℝ).1,1-(x : E × ℝ).2) := rfl

theorem productFiberReflection_involutive {E : Type*} [TopologicalSpace E] (A : Set E) :
    Function.Involutive (productFiberReflection A) := by
  intro x
  apply Subtype.ext
  ext
  · rfl
  · change 1-(1-(x : E × ℝ).2) = (x : E × ℝ).2
    ring

def prismFiberReflection {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) : B ≃ₜ B :=
  H.symm.trans ((productFiberReflection A).trans H)

theorem prismFiberReflection_involutive {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) : Function.Involutive (prismFiberReflection H) := by
  intro x
  simp only [prismFiberReflection,Homeomorph.trans_apply,H.symm_apply_apply,
    productFiberReflection_involutive A (H.symm x),H.apply_symm_apply]

theorem prismFiberReflection_finitePL
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {A r B : Set E} (hA : IsFinitePLBallPair V A r)
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (hH : H.IsFinitePL) :
    (prismFiberReflection H).IsFinitePL := by
  obtain ⟨K,_,hK,hKs,_,_⟩ := hA.exists_finite_carrier_and_rim_complexes
  have hprod : (productFiberReflection A).IsFinitePL :=
    (Homeomorph.isFinitePL_setCongr rfl K hK hKs).prod (fiberFlip_finitePL true)
  exact hH.symm.trans (hprod.trans hH)

theorem prismFiberReflection_eq_iff_height
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    prismFiberReflection H x = x ↔ (H.symm x : E × ℝ).2 = 1/2 := by
  rw [←H.symm.injective.eq_iff]
  change H.symm (H (productFiberReflection A (H.symm x))) = H.symm x ↔ _
  rw [H.symm_apply_apply,Subtype.ext_iff,productFiberReflection_value,Prod.mk.injEq]
  simp only [true_and]
  constructor <;> intro h <;> linarith

theorem prismFiberReflection_on_global_rectangle
    {E : Type*} [TopologicalSpace E] {A B M : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (u t : I) :
    (prismFiberReflection H ⟨G ⟨(u,t),u.property,t.property⟩,hMB (G _).property⟩ : E) =
      G ⟨(u,unitInterval.symm t),u.property,(unitInterval.symm t).property⟩ := by
  have h0 := prism_inverse_on_global_rectangle H G hMB flip hformula u t
  have h1 := prism_inverse_on_global_rectangle H G hMB flip hformula u (unitInterval.symm t)
  apply congrArg (fun x : B => (x : E)) (a₂ :=
    ⟨G ⟨(u,unitInterval.symm t),u.property,(unitInterval.symm t).property⟩,hMB (G _).property⟩)
  apply H.symm.injective
  apply Subtype.ext
  change (H.symm (H (productFiberReflection A (H.symm _))) : E × ℝ) = _
  rw [H.symm_apply_apply,productFiberReflection_value,h0,h1]
  apply Prod.ext
  · rfl
  · cases flip <;> rfl

end PoincareConjecture.M76.PrismBelt
