import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInitialSegment

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FinitePiecewiseAffineOn.exists_small_endpoint_levels
    {f : E → ℝ} {s : Set E} (hf : FinitePiecewiseAffineOn f s)
    (a : ℝ →ᴬ[ℝ] E) (ha : MapsTo a (Icc (0 : ℝ) 1) s)
    (hzero : f (a 0) = 0) (hpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f (a t)) :
    ∃ η : ℝ, 0 < η ∧ ∃ m : ℝ, 0 < m ∧
      ∀ c ∈ Icc 0 η, c / m ∈ Ico (0 : ℝ) 1 ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          (f (a t) ≤ c ↔ t ≤ c / m) ∧
          (f (a t) = c ↔ t = c / m) ∧
          (c ≤ f (a t) ↔ c / m ≤ t) := by
  obtain ⟨δ, hδ, m, hm, hformula⟩ := hf.exists_positive_initial_slope a ha hzero hpos
  have hcont : ContinuousOn (f ∘ a) (Icc (0 : ℝ) 1) :=
    hf.continuousOn.comp a.continuous.continuousOn ha
  obtain ⟨b, hb, hbound⟩ := isCompact_Icc.exists_forall_le'
    (hcont.mono (Icc_subset_Icc hδ.1.le le_rfl))
    (fun t (ht : t ∈ Icc δ 1) => hpos t ⟨hδ.1.trans_le ht.1, ht.2⟩)
  let η := min (δ * m) b / 2
  have hmin : 0 < min (δ * m) b := lt_min (mul_pos hδ.1 hm) hb
  have hη : 0 < η := half_pos hmin
  have hηδ : η < δ * m := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hηb : η < b := (half_lt_self hmin).trans_le (min_le_right _ _)
  refine ⟨η, hη, m, hm, fun c hc => ?_⟩
  have hcm : c / m * m = c := div_mul_cancel₀ c hm.ne'
  have hcδ : c / m < δ := (div_lt_iff₀ hm).mpr (hc.2.trans_lt hηδ)
  refine ⟨⟨div_nonneg hc.1 hm.le, hcδ.trans_le hδ.2⟩, fun t ht => ?_⟩
  by_cases htδ : t ≤ δ
  · rw [hformula t ⟨ht.1, htδ⟩]
    refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro h <;> nlinarith
  · have hct : c / m < t := hcδ.trans (lt_of_not_ge htδ)
    have hcf : c < f (a t) :=
      (hc.2.trans_lt hηb).trans_le (hbound t ⟨(lt_of_not_ge htδ).le, ht.2⟩)
    exact ⟨iff_of_false hcf.not_ge hct.not_ge, iff_of_false hcf.ne' hct.ne',
      iff_of_true hcf.le hct.le⟩

end Geometry
