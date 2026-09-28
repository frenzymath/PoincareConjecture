import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeBall

set_option autoImplicit false

open Set Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem AffineMap.image_convexJoin (f : E →ᵃ[ℝ] F) (s t : Set E) :
    f '' convexJoin ℝ s t = convexJoin ℝ (f '' s) (f '' t) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, b, hb, hxab⟩ := mem_convexJoin.mp hx
    refine mem_convexJoin.mpr ⟨f a, mem_image_of_mem f ha, f b, mem_image_of_mem f hb, ?_⟩
    rw [← image_segment ℝ f]
    exact mem_image_of_mem f hxab
  · intro hz
    obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hzab⟩ := mem_convexJoin.mp hz
    rw [← image_segment ℝ f] at hzab
    obtain ⟨x, hx, rfl⟩ := hzab
    exact ⟨x, mem_convexJoin.mpr ⟨a, ha, b, hb, hx⟩, rfl⟩

namespace Set

variable [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.convexJoin_of_affine_level {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (A : E →ᵃ[ℝ] ℝ)
    (p : E) {c : ℝ} (hpc : A p ≠ c) (hA : ∀ x ∈ d, A x = c) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (convexJoin ℝ {p} d)
      (d ∪ convexJoin ℝ {p} q) := by
  let down : E →ᴬ[ℝ] E := ContinuousAffineMap.id ℝ E - ContinuousAffineMap.const ℝ E p
  let up : E →ᴬ[ℝ] E := ContinuousAffineMap.id ℝ E + ContinuousAffineMap.const ℝ E p
  have hdown : Function.Injective down := by
    intro x y h
    have h' := congrArg (fun z : E => z + p) (show x - p = y - p from h)
    simpa only [sub_add_cancel] using h'
  have hup : Function.Injective up := by
    intro x y h
    exact add_right_cancel (show x + p = y + p from h)
  have hpair := hd.affine_image down hdown.injOn
  let L : E →ₗ[ℝ] ℝ := (c - A p)⁻¹ • A.linear
  have hL : ∀ x ∈ down '' d, L x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change (c - A p)⁻¹ * A.linear (x - p) = 1
    have hdiff : A.linear (x - p) = A x - A p := by
      simpa only [vsub_eq_sub] using A.linearMap_vsub x p
    rw [hdiff, hA x hx, inv_mul_cancel₀ (sub_ne_zero.mpr hpc.symm)]
  have hcone := (hpair.convexJoin_zero L hL).affine_image up hup.injOn
  have him (s : Set E) : up '' (down '' s) = s := by
    rw [image_image]
    exact (image_congr (fun x _ => show up (down x) = x by simp [up, down])).trans (image_id s)
  have hjoin (s : Set E) :
      up '' convexJoin ℝ {0} (down '' s) = convexJoin ℝ {p} s := by
    change (up : E →ᵃ[ℝ] E) '' convexJoin ℝ {0} (down '' s) = _
    rw [(up : E →ᵃ[ℝ] E).image_convexJoin, image_singleton]
    change convexJoin ℝ {up 0} (up '' (down '' s)) = convexJoin ℝ {p} s
    rw [him]
    simp [up]
  rwa [image_union, hjoin d, him d, hjoin q] at hcone

end Set
