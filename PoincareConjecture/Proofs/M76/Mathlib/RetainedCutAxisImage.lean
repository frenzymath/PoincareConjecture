import PoincareConjecture.Proofs.M76.Mathlib.RetainedLongitudinalPrism
import PoincareConjecture.Proofs.M76.Mathlib.LongitudinalPrismCoordinates












set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem image_axis_inverse_of_linear_cones
    {S : Set E} {T : Set ((ℝ × ℝ) × ℝ)} (e : S ≃ₜ T)
    (g : ((ℝ × ℝ) × ℝ) → E) (hg : ∀ y : T, g y = (e.symm y : E))
    (hcv : Convex ℝ S) (hzero : (0 : E) ∈ S)
    (Q : Bool → Set E) (p a : Bool → E)
    (hpS : ∀ j, p j ∈ S) (hpQ : ∀ j, p j ∈ Q j)
    (ρ : Bool → ℝ) (hρ : ∀ j, 1 < ρ j) (hpa : ∀ j, p j = ρ j • a j)
    (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hkeep : ∀ j (x : S), (x : E) ∈ convexJoin ℝ {0} (Q j) →
      (e x : (ℝ × ℝ) × ℝ) = L j x)
    (σ : Bool → ℝ) (hσneg : σ false < 0) (hσpos : 0 < σ true)
    (hLa : ∀ j, L j (a j) = ((0, σ j), 0)) :
    g '' (({0} ×ˢ Icc (σ false) (σ true)) ×ˢ {0}) =
      segment ℝ 0 (a false) ∪ segment ℝ 0 (a true) := by
  have hsegment (j : Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g ((0, t * σ j), 0) = t • a j := by
    have hρpos : 0 < ρ j := zero_lt_one.trans (hρ j)
    let c : ℝ := t / ρ j
    have hc0 : 0 ≤ c := div_nonneg ht.1 hρpos.le
    have hc1 : c ≤ 1 := (div_le_one₀ hρpos).mpr (ht.2.trans (hρ j).le)
    have hxS : c • p j ∈ S := by
      simpa only [smul_zero, zero_add] using hcv hzero (hpS j)
        (sub_nonneg.mpr hc1) hc0 (sub_add_cancel 1 c)
    have hxQ : c • p j ∈ convexJoin ℝ {0} (Q j) := by
      apply segment_subset_convexJoin (mem_singleton (0 : E)) (hpQ j)
      exact ⟨1 - c, c, sub_nonneg.mpr hc1, hc0, sub_add_cancel 1 c, by simp⟩
    have hxval : c • p j = t • a j := by
      change (t / ρ j) • p j = t • a j
      rw [hpa j, smul_smul, div_mul_cancel₀ _ hρpos.ne']
    let x : S := ⟨c • p j, hxS⟩
    have hmap : (e x : (ℝ × ℝ) × ℝ) = ((0, t * σ j), 0) := by
      rw [hkeep j x hxQ]
      change L j (c • p j) = _
      rw [hxval, map_smul, hLa j]
      simp only [Prod.smul_mk, smul_eq_mul, mul_zero]
    calc
      g ((0, t * σ j), 0) = g (e x) := congrArg g hmap.symm
      _ = (e.symm (e x) : E) := hg (e x)
      _ = (x : E) := congrArg Subtype.val (e.symm_apply_apply x)
      _ = t • a j := hxval
  have hseg (j : Bool) : segment ℝ (0 : E) (a j) =
      (fun t : ℝ => t • a j) '' Icc (0 : ℝ) 1 := by
    simpa only [smul_zero, zero_add] using segment_eq_image ℝ (0 : E) (a j)
  have haxis (j : Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (((0 : ℝ), t * σ j), (0 : ℝ)) ∈
        ({(0 : ℝ)} ×ˢ Icc (σ false) (σ true)) ×ˢ {(0 : ℝ)} := by
    refine ⟨⟨rfl, ?_⟩, rfl⟩
    cases j <;> constructor <;> nlinarith [ht.1, ht.2]
  apply Subset.antisymm
  · rintro _ ⟨⟨⟨u, s⟩, z⟩, ⟨⟨hu, hs⟩, hz⟩, rfl⟩
    have hu0 : u = 0 := hu
    have hz0 : z = 0 := hz
    subst u
    subst z
    by_cases hs0 : s ≤ 0
    · have ht : s / σ false ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg_of_nonpos hs0 hσneg.le, (div_le_one_of_neg hσneg).mpr hs.1⟩
      have hvalue := hsegment false (s / σ false) ht
      rw [div_mul_cancel₀ s hσneg.ne] at hvalue
      apply Or.inl
      rw [hseg false, hvalue]
      exact mem_image_of_mem _ ht
    · have ht : s / σ true ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (le_of_not_ge hs0) hσpos.le, (div_le_one₀ hσpos).mpr hs.2⟩
      have hvalue := hsegment true (s / σ true) ht
      rw [div_mul_cancel₀ s hσpos.ne'] at hvalue
      apply Or.inr
      rw [hseg true, hvalue]
      exact mem_image_of_mem _ ht
  · have hsub (j : Bool) : segment ℝ (0 : E) (a j) ⊆
        g '' (({0} ×ˢ Icc (σ false) (σ true)) ×ˢ {0}) := by
      rw [hseg j]
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨((0, t * σ j), 0), haxis j t ht, hsegment j t ht⟩
    exact union_subset (hsub false) (hsub true)

end Homeomorph

namespace CoordinateHalfBoxes




theorem longitudinalPrismCoordinates_image_axis {r a b : ℝ}
    (hr : 0 < r) (hab : a < b) :
    longitudinalPrismCoordinates r a b '' (({0} ×ˢ Icc (-r) r) ×ˢ {0}) =
      ({0} ×ˢ Icc a b) ×ˢ {0} := by
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have himage := (longitudinalPrismCoordinates_properties hr hab).2.1
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxt : x.1.1 = 0 := hx.1.1
    have hxz : x.2 = 0 := hx.2
    have hxbox : x ∈ box r :=
      ⟨⟨hxt.symm ▸ hzero, hx.1.2⟩, hxz.symm ▸ hzero⟩
    have hy := himage.subset (mem_image_of_mem _ hxbox)
    exact ⟨⟨hx.1.1, hy.1.2⟩, hx.2⟩
  · intro y hy
    have hyt : y.1.1 = 0 := hy.1.1
    have hyz : y.2 = 0 := hy.2
    have hyprism : y ∈ (Icc (-r) r ×ˢ Icc a b) ×ˢ Icc (-r) r :=
      ⟨⟨hyt.symm ▸ hzero, hy.1.2⟩, hyz.symm ▸ hzero⟩
    obtain ⟨x, hx, hxy⟩ := himage.symm.subset hyprism
    have hfirst : x.1.1 = y.1.1 := by
      simpa only [longitudinalPrismCoordinates_apply] using
        congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) hxy
    have hlast : x.2 = y.2 := by
      simpa only [longitudinalPrismCoordinates_apply] using
        congrArg (fun z : (ℝ × ℝ) × ℝ => z.2) hxy
    exact ⟨x, ⟨⟨hfirst.trans hy.1.1, hx.1.2⟩, hlast.trans hy.2⟩, hxy⟩

end CoordinateHalfBoxes
