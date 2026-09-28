import PoincareConjecture.Proofs.M76.Mathlib.CoreRadialCompression
import PoincareConjecture.Proofs.M76.Mathlib.ProjectiveConvexHull

set_option autoImplicit false

open Set

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coreCompression_eq_fractionalRadial (L : E →ₗ[ℝ] ℝ) {x : E}
    (hx : 1 ≤ L x) (he : ‖x‖ = L x) :
    coreCompression x = (2 : ℝ) • L.fractionalRadial x := by
  rw [coreCompression_of_one_le_norm (he ▸ hx), he,
    LinearMap.fractionalRadial, smul_smul, div_eq_mul_inv]

theorem coreCompression_simplex (s : Finset E)
    (hind : AffineIndependent ℝ ((↑) : s → E))
    (hsector : (∀ x ∈ convexHull ℝ (s : Set E), ‖x‖ ≤ 1) ∨
      ∃ L : E →ₗ[ℝ] ℝ, ∀ x ∈ convexHull ℝ (s : Set E), 1 ≤ L x ∧ ‖x‖ = L x) :
    AffineIndependent ℝ ((↑) : ↥(coreCompression '' (s : Set E)) → E) ∧
      coreCompression '' convexHull ℝ (s : Set E) =
        convexHull ℝ (coreCompression '' (s : Set E)) := by
  classical
  rcases hsector with hcore | ⟨L, hL⟩
  · have hc : EqOn (coreCompression : E → E) id (convexHull ℝ (s : Set E)) :=
      fun x hx => coreCompression_of_norm_le_one (hcore x hx)
    have hverts := hc.mono (subset_convexHull ℝ (s : Set E))
    have hi : coreCompression '' (s : Set E) = (s : Set E) :=
      hverts.image_eq.trans (image_id _)
    rw [hi]
    exact ⟨hind, hc.image_eq.trans (image_id _)⟩
  · let a : E →ᵃ[ℝ] E := (2 : ℝ) • AffineMap.id ℝ E
    have ha : Function.Injective a := smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)
    have hd (x : E) (hx : x ∈ (s : Set E)) : 0 < 1 + L x := by
      have h := (hL x (subset_convexHull ℝ _ hx)).1
      linarith
    have hc : EqOn coreCompression (a ∘ L.fractionalRadial)
        (convexHull ℝ (s : Set E)) := by
      intro x hx
      exact coreCompression_eq_fractionalRadial L (hL x hx).1 (hL x hx).2
    have hverts := hc.mono (subset_convexHull ℝ (s : Set E))
    constructor
    · have h := (L.fractionalRadial_affineIndependent hind
          (fun i : s => (hd i i.property).ne')).map' a ha
      have he : a ∘ (L.fractionalRadial ∘ ((↑) : s → E)) =
          coreCompression ∘ ((↑) : s → E) := by
        funext v
        exact (hverts v.property).symm
      rw [he] at h
      have hr : range (coreCompression ∘ ((↑) : s → E)) =
          coreCompression '' (s : Set E) := by ext y; simp
      have h' := h.range
      change AffineIndependent ℝ ((↑) : range (coreCompression ∘ ((↑) : s → E)) → E) at h'
      rwa [hr] at h'
    · calc
        coreCompression '' convexHull ℝ (s : Set E) =
            (a ∘ L.fractionalRadial) '' convexHull ℝ (s : Set E) := hc.image_eq
        _ = a '' (L.fractionalRadial '' convexHull ℝ (s : Set E)) := by
          rw [image_image]
          rfl
        _ = a '' convexHull ℝ (L.fractionalRadial '' (s : Set E)) := by
          rw [L.fractionalRadial_image_convexHull hd]
        _ = convexHull ℝ (a '' (L.fractionalRadial '' (s : Set E))) := a.image_convexHull _
        _ = convexHull ℝ (coreCompression '' (s : Set E)) := by
          rw [image_image]
          exact congrArg (convexHull ℝ) hverts.image_eq.symm

end NormedSpace
