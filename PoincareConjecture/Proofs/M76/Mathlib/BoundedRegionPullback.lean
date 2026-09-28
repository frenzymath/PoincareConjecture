import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalTransport

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pullback_spherical_region_balls (H : E ≃ₜ E)
    (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space)
    {D U S : Set E} (hHD : H '' D = D)
    (hU : IsOpen U) (hUD : closure U ⊆ interior D)
    (hUf : frontier U = H '' S)
    (hUB : IsFinitePLBallPair F (closure U) (H '' S))
    (hUE : IsFinitePLBallPair F
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) ((H '' S) ×ˢ {1})) :
    IsOpen (H ⁻¹' U) ∧ frontier (H ⁻¹' U) = S ∧
      closure (H ⁻¹' U) ⊆ interior D ∧
      IsFinitePLBallPair F (closure (H ⁻¹' U)) S ∧
      IsFinitePLBallPair F
        (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ (H ⁻¹' U) ×ˢ {1}) (S ×ˢ {1}) := by
  have hpreD : H ⁻¹' D = D := by
    exact (congrArg (fun s : Set E => H ⁻¹' s) hHD.symm).trans (H.preimage_image D)
  have hpreInt : H ⁻¹' interior D = interior D := by
    rw [H.preimage_interior, hpreD]
  have hpreBound : closure (H ⁻¹' U) ⊆ interior D := by
    rw [← H.preimage_closure]
    exact (preimage_mono hUD).trans hpreInt.subset
  have hpreFront : frontier (H ⁻¹' U) = S := by
    rw [← H.preimage_frontier, hUf, H.preimage_image]
  have hB := hUB.preimage_of_finitePL_on_finite_polyhedra H hH
  rw [H.preimage_closure, H.preimage_image] at hB
  have hEiff := H.isFinitePLBallPair_cylinderComplement_image_iff (V := F)
    hH hHD (Icc (-1 : ℝ) 1) (1 : ℝ) (H ⁻¹' U) S
  simp only [← Set.prod_singleton, H.image_preimage] at hEiff
  exact ⟨hU.preimage H.continuous, hpreFront, hpreBound, hB, hEiff.mp hUE⟩

end Homeomorph
