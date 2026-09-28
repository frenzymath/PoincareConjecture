import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages










set_option autoImplicit false

open Set Geometry

namespace Set




theorem image_level_of_scaled_height {E F : Type*} {f : E → F}
    {s : Set E} {r : E → ℝ} {A : F → ℝ} {k : ℝ} (hk : k ≠ 0)
    (hheight : ∀ x ∈ s, A (f x) = k * r x) (t : ℝ) :
    f '' (s ∩ {x | r x = t}) = (f '' s) ∩ {y | A y = k * t} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxt⟩, rfl⟩
    exact ⟨mem_image_of_mem f hx, (hheight x hx).trans (congrArg (k * ·) hxt)⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxt⟩
    exact ⟨x, ⟨hx, mul_left_cancel₀ hk ((hheight x hx).symm.trans hxt)⟩, rfl⟩




theorem image_sublevel_of_scaled_height {E F : Type*} {f : E → F}
    {s : Set E} {r : E → ℝ} {A : F → ℝ} {k : ℝ} (hk : 0 < k)
    (hheight : ∀ x ∈ s, A (f x) = k * r x) (t : ℝ) :
    f '' (s ∩ {x | r x ≤ t}) = (f '' s) ∩ {y | A y ≤ k * t} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxt⟩, rfl⟩
    exact ⟨mem_image_of_mem f hx,
      (hheight x hx).le.trans (mul_le_mul_of_nonneg_left hxt hk.le)⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxt⟩
    exact ⟨x, ⟨hx, (mul_le_mul_iff_right₀ hk).mp (by rwa [← hheight x hx])⟩, rfl⟩

end Set

namespace Geometry

variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]





theorem FinitePiecewiseAffineOn.image_level_ballPair {f : E → F} {S d b : Set E}
    (hf : FinitePiecewiseAffineOn f S) (hinj : InjOn f S) (hdS : d ⊆ S) (hb : b ⊆ d)
    {r : E → ℝ} {A : F → ℝ} {k t : ℝ} (hk : k ≠ 0)
    (hheight : ∀ x ∈ d, A (f x) = k * r x)
    (hlevel : IsFinitePLBallPair V (d ∩ {x | r x = t}) (b ∩ {x | r x = t})) :
    IsFinitePLBallPair V ((f '' d) ∩ {y | A y = k * t})
      ((f '' b) ∩ {y | A y = k * t}) := by
  have h := hlevel.image_of_subset hf (inter_subset_left.trans hdS) hinj
  rwa [image_level_of_scaled_height hk hheight,
    image_level_of_scaled_height hk (fun x hx => hheight x (hb hx))] at h




theorem FinitePiecewiseAffineOn.image_sublevel_ballPair {f : E → F} {S d : Set E}
    (hf : FinitePiecewiseAffineOn f S) (hinj : InjOn f S) (hdS : d ⊆ S)
    {r : E → ℝ} {A : F → ℝ} {k t : ℝ} (hk : 0 < k)
    (hheight : ∀ x ∈ d, A (f x) = k * r x)
    (hlevel : IsFinitePLBallPair V (d ∩ {x | r x ≤ t}) (d ∩ {x | r x = t})) :
    IsFinitePLBallPair V ((f '' d) ∩ {y | A y ≤ k * t})
      ((f '' d) ∩ {y | A y = k * t}) := by
  have h := hlevel.image_of_subset hf (inter_subset_left.trans hdS) hinj
  rwa [image_sublevel_of_scaled_height hk hheight,
    image_level_of_scaled_height hk.ne' hheight] at h

end Geometry
