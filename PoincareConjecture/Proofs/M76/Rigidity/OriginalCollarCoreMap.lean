import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.CubeCollarInnerExtension

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "B" => closedBall (0 : V3) 1
local notation "B0" => closedBall (0 : V3) (7 / 8)
local notation "Q" => sphere (0 : V3) 1
local notation "Q0" => sphere (0 : V3) (7 / 8)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {C S : Set X}

theorem ChartwisePLBall.exists_inner_cube_map (b : ChartwisePLBall e C S)
    (β : Q ≃ₜ Q0) (A : B0 ≃ₜ B) (hA : A.IsFinitePL)
    (hAβ : ∀ z : Q, (A ⟨β z, sphere_subset_closedBall (β z).property⟩ : V3) = z)
    (hAmem : ∀ x : B0, (A x : V3) ∈ Q ↔ (x : V3) ∈ Q0) :
    ∃ f : V3 → X, PolyhedralPLInCharts e f B0 ∧ InjOn f B0 ∧
      f '' B0 = C ∧ (∀ x ∈ B0, f x ∈ S ↔ x ∈ Q0) ∧
      ∀ z : Q, f (β z) = b.map z := by
  obtain ⟨a, ha, haval⟩ := hA
  have hamap : MapsTo a B0 B := by
    intro x hx
    rw [← haval ⟨x, hx⟩]
    exact (A ⟨x, hx⟩).property
  let f : V3 → X := b.map ∘ a
  have hvalue (x : B0) : f x = (b.parametrization (A x) : X) := by
    change b.map (a x) = _
    rw [← haval x, b.map_eq]
  have haCopy := ha
  obtain ⟨K, hK, hKB, _⟩ := haCopy
  have hf : PolyhedralPLInCharts e f B0 := by
    have h := b.piecewiseAffine.comp_finitePiecewiseAffineOn K hK
      (hKB.symm ▸ ha) (fun _ hx => hamap (hKB.subset hx))
    exact hKB ▸ h
  have hi : InjOn f B0 := by
    intro x hx y hy hxy
    rw [hvalue ⟨x, hx⟩, hvalue ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (A.injective (b.parametrization.injective (Subtype.ext hxy)))
  have himage : f '' B0 = C := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hvalue ⟨z, hz⟩]
      exact (b.parametrization (A ⟨z, hz⟩)).property
    · intro hx
      let z : B0 := A.symm (b.parametrization.symm ⟨x, hx⟩)
      refine ⟨z, z.property, ?_⟩
      rw [hvalue z]
      change (b.parametrization (A (A.symm (b.parametrization.symm ⟨x, hx⟩))) : X) = x
      rw [A.apply_symm_apply, b.parametrization.apply_symm_apply]
  refine ⟨f, hf, hi, himage, ?_, ?_⟩
  · intro x hx
    rw [hvalue ⟨x, hx⟩]
    exact (b.boundary_eq (A ⟨x, hx⟩)).trans (hAmem ⟨x, hx⟩)
  · intro z
    rw [hvalue ⟨β z, sphere_subset_closedBall (β z).property⟩]
    have hAz : A ⟨β z, sphere_subset_closedBall (β z).property⟩ =
        ⟨z, sphere_subset_closedBall z.property⟩ := Subtype.ext (hAβ z)
    rw [hAz]
    exact (b.map_eq ⟨z, sphere_subset_closedBall z.property⟩).symm

end PoincareConjecture.M76
