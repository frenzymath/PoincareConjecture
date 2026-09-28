import PoincareConjecture.Proofs.M76.Mathlib.CoordinateSecondReflection

set_option autoImplicit false

open Set

namespace CoordinateHalfBoxes

noncomputable def transverseReflection : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)).prodCongr
    (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ)

theorem transverseReflection_apply (x : (ℝ × ℝ) × ℝ) :
    transverseReflection x = (x.1, -x.2) := rfl

theorem transverseReflection_involutive : Function.Involutive transverseReflection := by
  intro x
  simp only [transverseReflection_apply, neg_neg, Prod.eta]

theorem transverseReflection_zero : transverseReflection 0 = 0 :=
  map_zero transverseReflection

theorem transverseReflection_mem_box (r : ℝ) (x : (ℝ × ℝ) × ℝ) :
    transverseReflection x ∈ box r ↔ x ∈ box r := by
  simp only [box_eq_closedBall, Metric.mem_closedBall, dist_zero_right,
    transverseReflection_apply, Prod.norm_def, norm_neg]

theorem transverseReflection_image_box (r : ℝ) :
    transverseReflection '' box r = box r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (transverseReflection_mem_box r y).mpr hy
  · intro hx
    exact ⟨transverseReflection x, (transverseReflection_mem_box r x).mpr hx,
      transverseReflection_involutive x⟩

theorem transverseReflection_secondReflection (x : (ℝ × ℝ) × ℝ) :
    transverseReflection (secondReflection x) =
      secondReflection (transverseReflection x) := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem image_transverseReflection_trans (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (r : ℝ) :
    (transverseReflection.toContinuousAffineEquiv.trans f) '' box r = f '' box r := by
  change (f ∘ transverseReflection) '' box r = f '' box r
  rw [image_comp, transverseReflection_image_box]

end CoordinateHalfBoxes
