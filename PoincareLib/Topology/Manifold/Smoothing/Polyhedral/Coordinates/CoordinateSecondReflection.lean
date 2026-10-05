import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.CoordinateHalfBoxes

/-!
# Reversing only the along-section coordinate

The second-coordinate reflection retains the numerical height,
the transverse surface coordinate, and every complete centered
box. See Alexander 1924, pp. 6--8, Hudson 1969, pp. 12--19,
and M76 derivation 286f.
-/

set_option autoImplicit false

open Set

namespace CoordinateHalfBoxes

/-- Reflect the second coordinate only. The first coordinate
is the literal height and the last is the surface transverse
coordinate. See M76 derivation 286f. -/
noncomputable def secondReflection : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)

/-- The exact coordinate formula retains height and surface
transverse coordinate. See M76 derivation 286f. -/
theorem secondReflection_apply (x : (ℝ × ℝ) × ℝ) :
    secondReflection x = ((x.1.1, -x.1.2), x.2) := rfl

/-- The same reflection is its own inverse.
See M76 derivation 286f. -/
theorem secondReflection_involutive : Function.Involutive secondReflection := by
  intro x
  simp only [secondReflection_apply, neg_neg]

/-- The coordinate origin is fixed by the reflection.
See M76 derivation 286f. -/
theorem secondReflection_zero : secondReflection 0 = 0 := by
  exact map_zero secondReflection

/-- Reflection preserves membership in every whole centered
coordinate box, including its outer faces. See derivation 286f. -/
theorem secondReflection_mem_box (r : ℝ) (x : (ℝ × ℝ) × ℝ) :
    secondReflection x ∈ box r ↔ x ∈ box r := by
  simp only [box_eq_closedBall, Metric.mem_closedBall, dist_zero_right,
    secondReflection_apply, Prod.norm_def, norm_neg]

/-- The image of a whole centered box is that exact same box.
No radius or boundary face changes. See M76 derivation 286f. -/
theorem secondReflection_image_box (r : ℝ) : secondReflection '' box r = box r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (secondReflection_mem_box r y).mpr hy
  · intro hx
    exact ⟨secondReflection x, (secondReflection_mem_box r x).mpr hx,
      secondReflection_involutive x⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Precomposing an actual affine chart with the reflection
retains every whole image box literally. See derivation 286f. -/
theorem image_secondReflection_trans (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (r : ℝ) :
    (secondReflection.toContinuousAffineEquiv.trans f) '' box r = f '' box r := by
  change (f ∘ secondReflection) '' box r = f '' box r
  rw [image_comp, secondReflection_image_box]

/-- The reflected inverse chart negates only the old second
coordinate. See the orientation calculation in derivation 286f. -/
theorem secondReflection_trans_symm_apply
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (x : E) :
    (secondReflection.toContinuousAffineEquiv.trans f).symm x =
      secondReflection (f.symm x) := rfl

end CoordinateHalfBoxes
