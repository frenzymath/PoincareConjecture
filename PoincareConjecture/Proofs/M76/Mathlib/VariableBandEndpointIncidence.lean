import PoincareConjecture.Proofs.M76.Mathlib.VariableHeightBand

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FinitePiecewiseAffineOn.exists_variable_band_level_endpoint_charts
    {g : E × ℝ → ℝ} {B : Set E} {lower upper : E → ℝ}
    (hlu : ∀ x ∈ B, lower x ≤ upper x)
    (hg : FinitePiecewiseAffineOn g
      {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ c : ℝ,
      ∃ H : {x : E | x ∈ B ∧ c ∈ Icc (lower x + ε * g (x, lower x))
          (upper x + ε * g (x, upper x))} ≃ₜ
        ({p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} ∩
          {p : E × ℝ | p.2 + ε * g p = c} : Set (E × ℝ)),
        H.IsFinitePL ∧ (∀ x, (H x : E × ℝ).1 = (x : E)) ∧
          (∀ x : {x : E | x ∈ B ∧ c ∈ Icc (lower x + ε * g (x, lower x))
              (upper x + ε * g (x, upper x))},
            lower x + ε * g (x, lower x) = c ↔ (H x : E × ℝ).2 = lower x) ∧
          ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (lower x + ε * g (x, lower x))
              (upper x + ε * g (x, upper x))},
            upper x + ε * g (x, upper x) = c ↔ (H x : E × ℝ).2 = upper x := by
  obtain ⟨δ₁, hδ₁, hcharts⟩ := hg.exists_variable_band_level_charts hlu
  obtain ⟨δ₂, hδ₂, hmono⟩ := hg.exists_strictMonoOn_band_perturbation
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ε hε c => ?_⟩
  have hε₁ : |ε| < δ₁ := hε.trans_le (min_le_left _ _)
  have hε₂ : |ε| < δ₂ := hε.trans_le (min_le_right _ _)
  obtain ⟨H, hH, hbase⟩ := hcharts ε hε₁ c
  have hheight (x : {x : E | x ∈ B ∧ c ∈ Icc (lower x + ε * g (x, lower x))
      (upper x + ε * g (x, upper x))}) :
      (H x : E × ℝ).2 + ε * g ((x : E), (H x : E × ℝ).2) = c := by
    have hpair : ((x : E), (H x : E × ℝ).2) = (H x : E × ℝ) :=
      Prod.ext (hbase x).symm rfl
    rw [hpair]
    exact (H x).property.2
  have hdomain (x : {x : E | x ∈ B ∧ c ∈ Icc (lower x + ε * g (x, lower x))
      (upper x + ε * g (x, upper x))}) :
      (H x : E × ℝ).2 ∈ Icc (lower x) (upper x) := by
    have h := (H x).property.1.2
    rwa [hbase x] at h
  refine ⟨H, hH, hbase, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      exact (hmono ε hε₂ x x.property.1).injOn (hdomain x)
        ⟨le_rfl, hlu x x.property.1⟩ ((hheight x).trans hx.symm)
    · intro hx
      simpa only [hx] using hheight x
  · intro x
    constructor
    · intro hx
      exact (hmono ε hε₂ x x.property.1).injOn (hdomain x)
        ⟨hlu x x.property.1, le_rfl⟩ ((hheight x).trans hx.symm)
    · intro hx
      simpa only [hx] using hheight x

end Geometry
