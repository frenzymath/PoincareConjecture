import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace PoincareConjecture

open Filter Set
open scoped Topology

noncomputable def horizon_scalarComparisonRhs (t z : ℝ) : ℝ :=
  -2 * Real.pi + 3 * z / (1 + 4 * t)

structure HorizonRegularSlabInput (a b : ℝ) where
  ordered : a ≤ b
  f : ℝ → ℝ
  f_continuous : ContinuousOn f (Icc a b)
  G : ℝ → ℝ
  clock_positive : ∀ t, t ∈ Icc a b → 0 < 1 + 4 * t
  initial_comparison : f a ≤ G a
  profile_continuous : ContinuousOn G (Icc a b)
  forward_difference : ∀ (s : ℝ), s ∈ Icc a b → s < b →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t, t ∈ Icc a b → s < t → t < s + δ →
        (f t - f s) / (t - s) ≤ horizon_scalarComparisonRhs s (f s) + ε
  profile_equation : ∀ t, t ∈ Icc a b →
    HasDerivWithinAt G (horizon_scalarComparisonRhs t (G t)) (Icc a b) t

structure HorizonRegularSlabConclusion {a b : ℝ}
    (I : HorizonRegularSlabInput a b) where
  comparison : ∀ t, t ∈ Icc a b → I.f t ≤ I.G t

private lemma hasDerivWithinAt_Ici_of_Icc
    {f : ℝ → ℝ} {d : ℝ} {a b t : ℝ}
    (h : HasDerivWithinAt f d (Icc a b) t) (ht : t ∈ Ico a b) :
    HasDerivWithinAt f d (Ici t) t := by
  apply h.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Ioo (a - 1) b, Ioo_mem_nhds (by linarith [ht.1]) ht.2, ?_⟩
  intro s hs
  exact ⟨ht.1.trans hs.2, le_of_lt hs.1.2⟩

private lemma clock_coefficient_le_left
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc a b)
    (hpos : ∀ s, s ∈ Icc a b → 0 < 1 + 4 * s) :
    3 / (1 + 4 * t) ≤ 3 / (1 + 4 * a) := by
  have hta : a ≤ t := ht.1
  have ha : 0 < 1 + 4 * a := hpos a ⟨le_rfl, hab⟩
  have ht' : 0 < 1 + 4 * t := hpos t ht
  apply (div_le_div_iff₀ ht' ha).2
  nlinarith

theorem horizon_regularSlabComparison : ∀ (a b : ℝ) (I : HorizonRegularSlabInput a b),
    Nonempty (HorizonRegularSlabConclusion I) := by
  intro a b I
  refine ⟨⟨?_⟩⟩
  rcases le_or_gt a b with hab | hba
  · have hforward : ∀ s ∈ Ico a b, ∀ r, horizon_scalarComparisonRhs s (I.f s) < r →
        ∃ᶠ z in 𝓝[>] s, slope I.f s z < r := by
      intro s hs r hr
      obtain ⟨δ, hδ, hquot⟩ := I.forward_difference s (Ico_subset_Icc_self hs) hs.2
        ((r - horizon_scalarComparisonRhs s (I.f s)) / 2) (by linarith)
      have hev : ∀ᶠ z in 𝓝[>] s, z ∈ Ioo s (min b (s + δ)) :=
        Ioo_mem_nhdsGT (lt_min hs.2 (by linarith))
      have hlt : ∀ᶠ z in 𝓝[>] s, (I.f z - I.f s) / (z - s) < r := by
        filter_upwards [hev] with z hz
        have hle := hquot z
          ⟨le_of_lt (lt_of_le_of_lt hs.1 hz.1),
            le_of_lt (lt_of_lt_of_le hz.2 (min_le_left _ _))⟩
          hz.1 (lt_of_lt_of_le hz.2 (min_le_right _ _))
        linarith
      simpa only [slope_def_field] using hlt.frequently
    have hprofile_Ici : ∀ s ∈ Ico a b,
        HasDerivWithinAt I.G (horizon_scalarComparisonRhs s (I.G s)) (Ici s) s := by
      intro s hs
      exact hasDerivWithinAt_Ici_of_Icc
        (I.profile_equation s (Ico_subset_Icc_self hs)) hs
    have hle : ∀ t ∈ Icc a b, I.f t ≤ I.G t := by
      let k : ℝ := 3 / (1 + 4 * a) + 1
      have hk : 0 < k := by
        dsimp [k]
        have := I.clock_positive a ⟨le_rfl, hab⟩
        positivity
      have hbarrier : ∀ ε : ℝ, 0 < ε → ε * Real.exp (2 * k * (b - a)) ≤ 1 →
          ∀ t ∈ Icc a b, I.f t ≤ I.G t + ε * Real.exp (2 * k * (t - a)) := by
        intro ε hε hεsmall t ht
        refine image_le_of_liminf_slope_right_lt_deriv_boundary'
          (f := I.f) (f' := fun s => horizon_scalarComparisonRhs s (I.f s))
          (B := fun s => I.G s + ε * Real.exp (2 * k * (s - a)))
          (B' := fun s => horizon_scalarComparisonRhs s (I.G s) +
            ε * (Real.exp (2 * k * (s - a)) * (2 * k)))
          I.f_continuous ?_ ?_ ?_ ?_ ?_ ht
        · exact hforward
        · simpa only [sub_self, mul_zero, Real.exp_zero, mul_one] using
            I.initial_comparison.trans (le_add_of_nonneg_right hε.le)
        · exact I.profile_continuous.add (by fun_prop)
        · intro s hs
          have hder : HasDerivAt (fun x : ℝ => ε * Real.exp (2 * k * (x - a)))
              (ε * (Real.exp (2 * k * (s - a)) * (2 * k))) s := by
            have hlin : HasDerivAt (fun x : ℝ => 2 * k * (x - a)) (2 * k) s := by
              simpa using ((hasDerivAt_id s).sub_const a).const_mul (2 * k)
            simpa [mul_assoc, mul_left_comm, mul_comm] using hlin.exp.const_mul ε
          exact (hprofile_Ici s hs).add hder.hasDerivWithinAt
        · intro s hs hcontact
          have hsI : s ∈ Icc a b := Ico_subset_Icc_self hs
          have hE : 0 < Real.exp (2 * k * (s - a)) := Real.exp_pos _
          have hEa : 0 < ε * Real.exp (2 * k * (s - a)) := by positivity
          have hcoef : 3 / (1 + 4 * s) < 2 * k := by
            have hlecoef := clock_coefficient_le_left hab hsI I.clock_positive
            dsimp [k]
            linarith
          have hEq : I.f s - I.G s = ε * Real.exp (2 * k * (s - a)) := by
            linarith [hcontact]
          dsimp [horizon_scalarComparisonRhs]
          have hden : 1 + 4 * s ≠ 0 := ne_of_gt (I.clock_positive s hsI)
          have hdenpos : 0 < 1 + 4 * s := I.clock_positive s hsI
          have hcoef_mul : 3 < 2 * k * (1 + 4 * s) :=
            (div_lt_iff₀ hdenpos).mp hcoef
          field_simp [hden]
          nlinarith [hEq, hcoef_mul, hEa, hdenpos]
      intro t ht
      refine le_of_forall_pos_le_add (fun δ hδ => ?_)
      have hEmax : 0 < Real.exp (2 * k * (b - a)) := Real.exp_pos _
      let ε : ℝ := min (Real.exp (2 * k * (b - a)))⁻¹
        (δ / Real.exp (2 * k * (b - a)))
      have hε : 0 < ε := by
        dsimp [ε]
        exact lt_min (by positivity) (by positivity)
      have hsmall : ε * Real.exp (2 * k * (b - a)) ≤ 1 := by
        dsimp [ε]
        calc
          min (Real.exp (2 * k * (b - a)))⁻¹
              (δ / Real.exp (2 * k * (b - a))) * Real.exp (2 * k * (b - a)) ≤
              (Real.exp (2 * k * (b - a)))⁻¹ * Real.exp (2 * k * (b - a)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hEmax.le
          _ = 1 := inv_mul_cancel₀ hEmax.ne'
      have hbar := hbarrier ε hε hsmall t ht
      have hEbound : ε * Real.exp (2 * k * (t - a)) ≤ δ := by
        have harg : 2 * k * (t - a) ≤ 2 * k * (b - a) := by nlinarith [ht.2]
        have hexp : Real.exp (2 * k * (t - a)) ≤ Real.exp (2 * k * (b - a)) :=
          Real.exp_le_exp.mpr harg
        dsimp [ε]
        calc
          min (Real.exp (2 * k * (b - a)))⁻¹
              (δ / Real.exp (2 * k * (b - a))) * Real.exp (2 * k * (t - a)) ≤
              (δ / Real.exp (2 * k * (b - a))) * Real.exp (2 * k * (b - a)) :=
            mul_le_mul (min_le_right _ _) hexp (by positivity) (by positivity)
          _ = δ := div_mul_cancel₀ δ hEmax.ne'
      linarith
    exact hle
  · intro t ht
    exact absurd ht (by simp [Icc_eq_empty_of_lt hba])

end PoincareConjecture
