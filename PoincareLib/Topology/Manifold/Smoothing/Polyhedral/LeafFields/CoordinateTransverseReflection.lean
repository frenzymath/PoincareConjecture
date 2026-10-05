import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.CoordinateSecondReflection

/-!
# Reversing only the transverse coordinate of a shared cut

Transverse reflection preserves the exact height, longitudinal
orientation and every complete centered box. It can therefore
be selected using the actual planar filling before the event
linear maps are fixed. See Alexander 1924, pp. 6--8, Hudson
1969, pp. 12--19 and M76 derivation 286ad.
-/

set_option autoImplicit false

open Set

namespace CoordinateHalfBoxes

/-- Reflect only the transverse coordinate. Both the literal
height and the oriented polygon coordinate are fixed.
See Alexander pp. 6--8 and derivation 286ad. -/
noncomputable def transverseReflection : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)).prodCongr
    (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ)

/-- The reflection's complete coordinate formula.
See M76 derivation 286ad. -/
theorem transverseReflection_apply (x : (ℝ × ℝ) × ℝ) :
    transverseReflection x = (x.1, -x.2) := rfl

/-- The transverse reflection is its own inverse.
See M76 derivation 286ad. -/
theorem transverseReflection_involutive : Function.Involutive transverseReflection := by
  intro x
  simp only [transverseReflection_apply, neg_neg, Prod.eta]

/-- The original cut origin is fixed.
See M76 derivation 286ad. -/
theorem transverseReflection_zero : transverseReflection 0 = 0 :=
  map_zero transverseReflection

/-- Every complete centered box has the same membership
after transverse reflection, including all boundary faces.
See M76 derivation 286ad. -/
theorem transverseReflection_mem_box (r : ℝ) (x : (ℝ × ℝ) × ℝ) :
    transverseReflection x ∈ box r ↔ x ∈ box r := by
  simp only [box_eq_closedBall, Metric.mem_closedBall, dist_zero_right,
    transverseReflection_apply, Prod.norm_def, norm_neg]

/-- The image of every centered box is literally unchanged.
See M76 derivation 286ad. -/
theorem transverseReflection_image_box (r : ℝ) :
    transverseReflection '' box r = box r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (transverseReflection_mem_box r y).mpr hy
  · intro hx
    exact ⟨transverseReflection x, (transverseReflection_mem_box r x).mpr hx,
      transverseReflection_involutive x⟩

/-- Transverse orientation does not alter the independently
selected longitudinal orientation. See derivation 286ad. -/
theorem transverseReflection_secondReflection (x : (ℝ × ℝ) × ℝ) :
    transverseReflection (secondReflection x) =
      secondReflection (transverseReflection x) := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Selecting the transverse orientation preserves the
whole original image box for every radius.
See Alexander pp. 6--8 and derivation 286ad. -/
theorem image_transverseReflection_trans (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (r : ℝ) :
    (transverseReflection.toContinuousAffineEquiv.trans f) '' box r = f '' box r := by
  change (f ∘ transverseReflection) '' box r = f '' box r
  rw [image_comp, transverseReflection_image_box]

end CoordinateHalfBoxes
