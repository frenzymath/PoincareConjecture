import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberInterpolation

set_option autoImplicit false
noncomputable section
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

def affineFiberHeight (r s : ℝ) : ℝ := (1-r)*s+r*(1-s)

theorem affineFiberHeight_flip (r : ℝ) (b : Bool) (s : I) :
    affineFiberHeight r (fiberFlip b s : ℝ) =
      if b then 1-affineFiberHeight r s else affineFiberHeight r s := by
  cases b
  · rfl
  · change (1-r)*(1-(s : ℝ))+r*(1-(1-(s : ℝ))) = 1-((1-r)*(s : ℝ)+r*(1-(s : ℝ)))
    ring

def prismAffineFiberPoint {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) (r : ℝ)
    (hr : affineFiberHeight r (H.symm x : E × ℝ).2 ∈ I) : B :=
  H ⟨((H.symm x : E × ℝ).1,affineFiberHeight r (H.symm x : E × ℝ).2),
    (H.symm x).property.1,hr⟩

theorem prismAffineFiberPoint_on_global_rectangle
    {E : Type*} [TopologicalSpace E] {A B M : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (u s : I) (r : ℝ)
    (hr : affineFiberHeight r (H.symm ⟨G ⟨(u,s),u.property,s.property⟩,
      hMB (G _).property⟩ : E × ℝ).2 ∈ I)
    (hs : affineFiberHeight r s ∈ I) :
    (prismAffineFiberPoint H ⟨G ⟨(u,s),u.property,s.property⟩,
      hMB (G _).property⟩ r hr : E) = G ⟨(u,affineFiberHeight r s),u.property,hs⟩ := by
  have h0 := prism_inverse_on_global_rectangle H G hMB flip hformula u s
  have h1 := prism_inverse_on_global_rectangle H G hMB flip hformula u ⟨_,hs⟩
  apply congrArg (fun x : B => (x : E)) (a₂ :=
    ⟨G ⟨(u,affineFiberHeight r s),u.property,hs⟩,hMB (G _).property⟩)
  apply H.symm.injective
  apply Subtype.ext
  simp only [prismAffineFiberPoint,H.symm_apply_apply,h0,h1]
  apply Prod.ext
  · rfl
  · rw [affineFiberHeight_flip]
    cases flip <;> rfl

theorem affineFiberHeight_rectangle_mem
    {E : Type*} [TopologicalSpace E] {A B M : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (u s : I) (r : ℝ)
    (hr : affineFiberHeight r (H.symm ⟨G ⟨(u,s),u.property,s.property⟩,
      hMB (G _).property⟩ : E × ℝ).2 ∈ I) : affineFiberHeight r s ∈ I := by
  have h0 := prism_inverse_on_global_rectangle H G hMB flip hformula u s
  rw [h0,affineFiberHeight_flip] at hr
  cases flip
  · exact hr
  · simp only [Bool.true_eq,ite_true] at hr
    constructor <;> linarith [hr.1,hr.2]

theorem prismAffineFiberPoint_on_affine_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B M : Set E} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip b : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (hside : ∀ t, (G (sidePoint b t) : E) =
      AffineMap.lineMap (G (sidePoint b 0) : E) (G (sidePoint b 1) : E) (t : ℝ))
    (s : I) (r : ℝ)
    (hr : affineFiberHeight r (H.symm ⟨G (sidePoint b s),hMB (G _).property⟩ : E × ℝ).2 ∈ I) :
    (prismAffineFiberPoint H ⟨G (sidePoint b s),hMB (G _).property⟩ r hr : E) =
      AffineMap.lineMap (G (sidePoint b s) : E)
        (prismFiberReflection H ⟨G (sidePoint b s),hMB (G _).property⟩ : E) r := by
  have hs : affineFiberHeight r s ∈ I := by
    cases b
    · exact affineFiberHeight_rectangle_mem H G hMB flip hformula 0 s r hr
    · exact affineFiberHeight_rectangle_mem H G hMB flip hformula 1 s r hr
  have hi : (prismAffineFiberPoint H ⟨G (sidePoint b s),hMB (G _).property⟩ r hr : E) =
      G (sidePoint b ⟨_,hs⟩) := by
    cases b
    · exact prismAffineFiberPoint_on_global_rectangle H G hMB flip hformula 0 s r hr hs
    · exact prismAffineFiberPoint_on_global_rectangle H G hMB flip hformula 1 s r hr hs
  rw [hi,prismFiberReflection_on_affine_side H G hMB flip b hformula hside s,
    hside ⟨_,hs⟩,hside s]
  simp only [AffineMap.lineMap_apply_module,affineFiberHeight]
  module

end PoincareConjecture.M76.PrismBelt
