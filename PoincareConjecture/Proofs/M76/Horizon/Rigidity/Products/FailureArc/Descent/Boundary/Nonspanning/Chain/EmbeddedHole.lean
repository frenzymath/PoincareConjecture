import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.HoleTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Fibers

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_inner_disk_image_of_copy
    {S T D : Set P2} (j : S → T) (hj : Function.Injective j)
    (hPL : ∃ f : P2 → P2, FinitePiecewiseAffineOn f S ∧ ∀ x : S, (j x : P2) = f x)
    (hD : IsFinitePLBallPair P2 D (frontier D)) (hDS : D ⊆ interior S) :
    ∃ (P : Set P2) (q : D ≃ₜ P),
      q.IsFinitePL ∧ IsFinitePLBallPair P2 P (frontier P) ∧ P ⊆ interior T ∧
      (∀ x : D, (q x : P2) = j ⟨x, interior_subset (hDS x.property)⟩) ∧
      (∀ x : S, (j x : P2) ∈ P ↔ (x : P2) ∈ D) ∧
      (∀ x : S, (j x : P2) ∈ interior P ↔ (x : P2) ∈ interior D) ∧
      (∀ x : S, (j x : P2) ∈ frontier P ↔ (x : P2) ∈ frontier D) ∧
      P = (fun x : S => (j x : P2)) '' (Subtype.val ⁻¹' D) := by
  obtain ⟨f, hf, hval⟩ := hPL
  have hfi : InjOn f S := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hj (Subtype.ext
      ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  obtain ⟨e, he, hev⟩ := hf.exists_homeomorph_image hfi
  obtain ⟨P, q, hq, hP, hPinside, hqv, hmem, hint, hfront⟩ :=
    exists_inner_disk_image e he hD hDS
  have heq (x : S) : (e x : P2) = j x := (hev x).trans (hval x).symm
  have him : f '' S ⊆ T := by
    rintro z ⟨x, hx, rfl⟩
    rw [← hval ⟨x, hx⟩]
    exact (j ⟨x, hx⟩).property
  refine ⟨P, q, hq, hP, hPinside.trans (interior_mono him), ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hqv x).trans (heq _)
  · intro x
    simpa only [heq] using hmem x
  · intro x
    simpa only [heq] using hint x
  · intro x
    simpa only [heq] using hfront x
  · ext z
    constructor
    · intro hz
      let x := q.symm ⟨z, hz⟩
      refine ⟨⟨x, interior_subset (hDS x.property)⟩, x.property, ?_⟩
      exact (heq _).symm.trans ((hqv x).symm.trans
        (congrArg Subtype.val (q.apply_symm_apply ⟨z, hz⟩)))
    · rintro ⟨x, hx, rfl⟩
      simpa only [heq] using (hmem x).mpr hx

end PoincareConjecture.M76.Dehn
