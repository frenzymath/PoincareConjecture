import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes










set_option autoImplicit false

open Set

namespace CoordinateHalfBoxes




noncomputable def secondReflection : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)



theorem secondReflection_apply (x : (ℝ × ℝ) × ℝ) :
    secondReflection x = ((x.1.1, -x.1.2), x.2) := rfl



theorem secondReflection_involutive : Function.Involutive secondReflection := by
  intro x
  simp only [secondReflection_apply, neg_neg]



theorem secondReflection_zero : secondReflection 0 = 0 := by
  exact map_zero secondReflection



theorem secondReflection_mem_box (r : ℝ) (x : (ℝ × ℝ) × ℝ) :
    secondReflection x ∈ box r ↔ x ∈ box r := by
  simp only [box_eq_closedBall, Metric.mem_closedBall, dist_zero_right,
    secondReflection_apply, Prod.norm_def, norm_neg]



theorem secondReflection_image_box (r : ℝ) : secondReflection '' box r = box r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (secondReflection_mem_box r y).mpr hy
  · intro hx
    exact ⟨secondReflection x, (secondReflection_mem_box r x).mpr hx,
      secondReflection_involutive x⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem image_secondReflection_trans (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (r : ℝ) :
    (secondReflection.toContinuousAffineEquiv.trans f) '' box r = f '' box r := by
  change (f ∘ secondReflection) '' box r = f '' box r
  rw [image_comp, secondReflection_image_box]



theorem secondReflection_trans_symm_apply
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (x : E) :
    (secondReflection.toContinuousAffineEquiv.trans f).symm x =
      secondReflection (f.symm x) := rfl

end CoordinateHalfBoxes
