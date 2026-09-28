import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.FilledModel

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Levels

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

def slice (S : Set E2) (z : Real) : Set E3 :=
  {y | WithLp.toLp 2 ![y 0, y 1] ∈ S ∧ y 2 = z}

theorem band_eq_iUnion_slices :
    band = ⋃ z ∈ Icc (-9 / 8 : Real) (1 / 2),
      slice {x : E2 | (x 0)^2 + (x 1)^2 + (z + (x 0)^2)^2 = 1} z := by
  ext y
  simp only [band, mem_setOf_eq, mem_iUnion, slice]
  constructor
  · rintro ⟨hy, hz⟩
    exact ⟨y 2, hz, hy, rfl⟩
  · rintro ⟨z, hz, hy, heq⟩
    subst z
    exact ⟨hy, hz⟩

theorem shear_image_sphere_eq_slices_union_caps :
    shear '' sphere (0 : E3) 1 =
      (⋃ z ∈ Icc (-9 / 8 : Real) (1 / 2),
        slice {x : E2 | (x 0)^2 + (x 1)^2 + (z + (x 0)^2)^2 = 1} z) ∪
      (lowerCap 1 '' closedBall (0 : E2) (Real.sqrt (1 / 8))) ∪
      (lowerCap (-1) '' closedBall (0 : E2) (Real.sqrt (1 / 8))) ∪
      (upperCap '' closedBall (0 : E2) (Real.sqrt (3 / 4))) := by
  rw [shear_image_sphere_eq_band_union_caps, band_eq_iUnion_slices]

end Poincare.Manifold.Schoenflies.Saddle.Levels
