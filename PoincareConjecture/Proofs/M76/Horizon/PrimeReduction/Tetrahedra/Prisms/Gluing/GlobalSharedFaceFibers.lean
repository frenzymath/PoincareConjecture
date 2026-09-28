import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalOriginalPrismFamily
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.CutComponentSidePairing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.MarkedDiskIncidence
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalExceptionalComponents

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem prism_inverse_on_global_rectangle
    {E : Type*} [TopologicalSpace E] {A B M : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (u t : I) :
    (H.symm ⟨G ⟨(u,t),u.property,t.property⟩,hMB (G _).property⟩ : E × ℝ) =
      ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),
        (fiberFlip flip t : ℝ)) := by
  simpa only [fiberFlip_apply_apply] using hformula u (fiberFlip flip t)

theorem whole_shared_face_fiber_transition
    {E : Type*} [TopologicalSpace E] (A B : Bool → Set E) {M : Set E}
    (H : ∀ b, (A b ×ˢ I : Set (E × ℝ)) ≃ₜ B b) (G : Square ≃ₜ M)
    (hMB : ∀ b, M ⊆ B b) (flip : Bool → Bool)
    (hformula : ∀ b (u t : I),
      ((H b).symm ⟨G ⟨(u,fiberFlip (flip b) t),u.property,(fiberFlip (flip b) t).property⟩,
        hMB b (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip (flip b) 0),u.property,(fiberFlip (flip b) 0).property⟩ : E),(t : ℝ))) :
    ∀ b c (u t : I),
      ((H c).symm ⟨G ⟨(u,fiberFlip (flip b) t),u.property,(fiberFlip (flip b) t).property⟩,
        hMB c (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip (flip c) 0),u.property,(fiberFlip (flip c) 0).property⟩ : E),
          (fiberFlip (flip c) (fiberFlip (flip b) t) : ℝ)) := by
  intro b c u t
  exact prism_inverse_on_global_rectangle (H c) G (hMB c) (flip c)
    (hformula c) u (fiberFlip (flip b) t)

end PoincareConjecture.M76.PrismBelt
