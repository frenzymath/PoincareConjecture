import PoincareConjecture.Proofs.M76.PrimeReduction.CompactNormalExtension

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_actual_width_normal_extension
    {s q : Set E} (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (e : s ≃ₜ s) (he : e.IsFinitePL)
    (hfix : ∀ x : s, (x : E) ∈ q → e x = x)
    {r : ℝ} (hr : 0 < r) :
    ∃ H : (s ×ˢ Icc (-r) r : Set (E × ℝ)) ≃ₜ (s ×ˢ Icc (-r) r),
      H.IsFinitePL ∧
      (∀ x : s, (H ⟨((x : E), 0), x.property, by linarith, hr.le⟩ : E × ℝ) =
        ((e x : E), 0)) ∧
      (∀ x : (s ×ˢ Icc (-r) r : Set (E × ℝ)),
        (x : E × ℝ).1 ∈ q ∨ (x : E × ℝ).2 = -r ∨ (x : E × ℝ).2 = r → H x = x) ∧
      ∀ x : (s ×ˢ Icc (-r) r : Set (E × ℝ)),
        (H x : E × ℝ).2 = 0 ↔ (x : E × ℝ).2 = 0 := by
  obtain ⟨H0, hH0, hH0zero, hH0fix, hH0iff⟩ :=
    hs.exists_compact_normal_extension e he hfix
  let j : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (r • ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap
  have hball := hs.prod (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  have hj : FinitePiecewiseAffineOn j (s ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine j⟩
  have hji : InjOn j (s ×ˢ Icc (-1 : ℝ) 1) := by
    intro x _ y _ h
    change (x.1, r * x.2) = (y.1, r * y.2) at h
    have ht := congrArg (fun z : E × ℝ => z.2) h
    have hf := congrArg (fun z : E × ℝ => z.1) h
    exact Prod.ext hf (mul_left_cancel₀ hr.ne' ht)
  have hjimage : j '' (s ×ˢ Icc (-1 : ℝ) 1) = s ×ˢ Icc (-r) r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hy.1, ?_⟩
      change -r ≤ r * y.2 ∧ r * y.2 ≤ r
      constructor <;> nlinarith [hy.2.1, hy.2.2]
    · rintro ⟨hx, ht⟩
      refine ⟨(x.1, x.2 / r), ⟨hx, ?_⟩, ?_⟩
      · constructor
        · apply (le_div_iff₀ hr).2
          nlinarith [ht.1]
        · apply (div_le_iff₀ hr).2
          simpa only [one_mul] using ht.2
      · change (x.1, r * (x.2 / r)) = x
        simp only [mul_div_cancel₀ _ hr.ne', Prod.mk.eta]
  have hjex := hj.exists_homeomorph_image hji
  rw [hjimage] at hjex
  obtain ⟨J, hJ, hJval⟩ := hjex
  have hJinv (x : (s ×ˢ Icc (-r) r : Set (E × ℝ))) :
      (J.symm x : E × ℝ) = ((x : E × ℝ).1, (x : E × ℝ).2 / r) := by
    have h := hJval (J.symm x)
    rw [J.apply_symm_apply] at h
    change (x : E × ℝ) = ((J.symm x : E × ℝ).1, r * (J.symm x : E × ℝ).2) at h
    refine Prod.ext (congrArg (fun z : E × ℝ => z.1) h).symm ?_
    have ht := congrArg (fun z : E × ℝ => z.2) h
    dsimp only at ht
    apply (eq_div_iff hr.ne').2
    nlinarith
  let H := J.symm.trans (H0.trans J)
  have hH : H.IsFinitePL := hJ.symm.trans (hH0.trans hJ)
  have hHval (x : (s ×ˢ Icc (-r) r : Set (E × ℝ))) :
      (H x : E × ℝ) = ((H0 (J.symm x) : E × ℝ).1,
        r * (H0 (J.symm x) : E × ℝ).2) := hJval (H0 (J.symm x))
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · intro x
    have hz : J.symm ⟨((x : E), 0), x.property, by linarith, hr.le⟩ =
        ⟨((x : E), 0), x.property, by norm_num, zero_le_one⟩ := by
      apply Subtype.ext
      rw [hJinv]
      simp only [zero_div]
    rw [hHval, hz, hH0zero]
    simp only [mul_zero]
  · intro x hx
    have hy : (J.symm x : E × ℝ).1 ∈ q ∨
        (J.symm x : E × ℝ).2 = -1 ∨ (J.symm x : E × ℝ).2 = 1 := by
      rw [hJinv]
      rcases hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by dsimp only; rw [h]; simp [hr.ne']))
      · exact Or.inr (Or.inr (by dsimp only; rw [h]; simp [hr.ne']))
    change J (H0 (J.symm x)) = x
    rw [hH0fix _ hy, J.apply_symm_apply]
  · intro x
    rw [hHval]
    change r * (H0 (J.symm x) : E × ℝ).2 = 0 ↔ (x : E × ℝ).2 = 0
    simp only [mul_eq_zero, false_or, hH0iff, hJinv, div_eq_zero_iff,
      hr.ne', or_false]

end Set
