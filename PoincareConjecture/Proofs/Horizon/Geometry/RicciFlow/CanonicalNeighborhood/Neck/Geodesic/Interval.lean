import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue












set_option autoImplicit false

open Set

namespace PoincareConjecture.EpsilonNeck

theorem exists_subinterval_of_two_mul_le {L h t : ℝ}
    (hh : 0 ≤ h) (hL : 2 * h ≤ L) (ht : t ∈ Icc 0 L) :
    ∃ a b : ℝ, 0 ≤ a ∧ b ≤ L ∧ b - a = h ∧ t ∈ Icc a b := by
  by_cases hf : t + h ≤ L
  · exact ⟨t, t + h, ht.1, hf, by ring, le_rfl, by linarith⟩
  · exact ⟨t - h, t, by linarith, ht.2, by ring, by linarith, le_rfl⟩



theorem abs_velocity_lower_bound_on_subinterval
    {f v : ℝ → ℝ} {a b t A C δ : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) (hA : 0 < A) (hδ : 0 ≤ δ)
    (hf : ∀ u ∈ Icc a b, HasDerivAt f (v u) u)
    (hv : ∀ u ∈ Icc a b, |v u - v t| ≤ δ * |u - t|)
    (hmin : b - a ≤ A * (|f b - f a| + C)) :
    A⁻¹ - C / (b - a) - δ * (b - a) ≤ |v t| := by
  have hvel (u : ℝ) (hu : u ∈ Icc a b) :
      ‖v u‖ ≤ |v t| + δ * (b - a) := by
    have hdist : |u - t| ≤ b - a := by
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
    calc
      ‖v u‖ = |v u| := Real.norm_eq_abs _
      _ ≤ |v u - v t| + |v t| := by
        simpa only [sub_add_cancel] using abs_add_le (v u - v t) (v t)
      _ ≤ δ * |u - t| + |v t| := add_le_add (hv u hu) le_rfl
      _ ≤ |v t| + δ * (b - a) := by
        linarith [mul_le_mul_of_nonneg_left hdist hδ]
  have hdisp := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hf u hu).hasDerivWithinAt) hvel
    (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
  simp only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at hdisp
  have hcomp : b - a ≤ A * ((|v t| + δ * (b - a)) * (b - a) + C) :=
    hmin.trans (mul_le_mul_of_nonneg_left (add_le_add hdisp le_rfl) hA.le)
  have hquot : (b - a) / A ≤ (|v t| + δ * (b - a)) * (b - a) + C :=
    (div_le_iff₀ hA).mpr (by simpa only [mul_comm A] using hcomp)
  have hh : 0 < b - a := sub_pos.mpr hab
  have hc : C / (b - a) * (b - a) = C := div_mul_cancel₀ C hh.ne'
  have ha : A⁻¹ * (b - a) = (b - a) / A := by ring
  apply (mul_le_mul_iff_left₀ hh).mp
  nlinarith



theorem abs_velocity_lower_bound
    {f v : ℝ → ℝ} {L h A C δ : ℝ}
    (hh : 0 < h) (hL : 2 * h ≤ L) (hA : 0 < A) (hδ : 0 ≤ δ)
    (hf : ∀ u ∈ Icc 0 L, HasDerivAt f (v u) u)
    (hv : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, |v s - v t| ≤ δ * |s - t|)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L,
      a ≤ b → b - a ≤ A * (|f b - f a| + C))
    {t : ℝ} (ht : t ∈ Icc 0 L) :
    A⁻¹ - C / h - δ * h ≤ |v t| := by
  obtain ⟨a, b, ha, hb, hba, ht'⟩ := exists_subinterval_of_two_mul_le hh.le hL ht
  have hab : a < b := by linarith
  have hsub : Icc a b ⊆ Icc 0 L := Icc_subset_Icc ha hb
  have ham : a ∈ Icc 0 L := hsub (left_mem_Icc.mpr hab.le)
  have hbm : b ∈ Icc 0 L := hsub (right_mem_Icc.mpr hab.le)
  simpa only [hba] using abs_velocity_lower_bound_on_subinterval hab ht' hA hδ
    (fun u hu => hf u (hsub hu)) (fun u hu => hv u (hsub hu) t ht)
    (hmin a ham b hbm hab.le)


theorem velocity_pos_of_abs_lower_bound
    {f v : ℝ → ℝ} {L k : ℝ} (hL : 0 < L) (hk : 0 < k)
    (hf : ∀ u ∈ Icc 0 L, HasDerivAt f (v u) u)
    (hv : ContinuousOn v (Icc 0 L))
    (habs : ∀ u ∈ Icc 0 L, k ≤ |v u|)
    (horient : f 0 < f L) : ∀ t ∈ Icc 0 L, 0 < v t := by
  have hcont : ContinuousOn f (Icc 0 L) :=
    fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Ioo 0 L) :=
    fun u hu => (hf u (Ioo_subset_Icc_self hu)).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope f hL hcont hdiff
  have hc' := Ioo_subset_Icc_self hc
  rw [(hf c hc').deriv] at heq
  have hvc : 0 < v c := by
    rw [heq]
    exact div_pos (sub_pos.mpr horient) (sub_pos.mpr hL)
  intro t ht
  by_contra h
  have hvt : v t ≤ 0 := le_of_not_gt h
  obtain ⟨u, hu, hzero⟩ := isPreconnected_Icc.intermediate_value ht hc' hv
    (show (0 : ℝ) ∈ Icc (v t) (v c) from ⟨hvt, hvc.le⟩)
  have hh := habs u hu
  rw [hzero, abs_zero] at hh
  linarith



theorem velocity_lower_bound
    {f v acc : ℝ → ℝ} {L h A C δ : ℝ}
    (hh : 0 < h) (hL : 2 * h ≤ L) (hA : 0 < A) (hδ : 0 ≤ δ)
    (hf : ∀ u ∈ Icc 0 L, HasDerivAt f (v u) u)
    (hv : ∀ u ∈ Icc 0 L, HasDerivAt v (acc u) u)
    (hacc : ∀ u ∈ Icc 0 L, |acc u| ≤ δ)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L,
      a ≤ b → b - a ≤ A * (|f b - f a| + C))
    (horient : f 0 < f L) (hpos : 0 < A⁻¹ - C / h - δ * h) :
    ∀ t ∈ Icc 0 L, A⁻¹ - C / h - δ * h ≤ v t := by
  have hLip (s : ℝ) (hs : s ∈ Icc 0 L) (t : ℝ) (ht : t ∈ Icc 0 L) :
      |v s - v t| ≤ δ * |s - t| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc (0 : ℝ) L).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u hu => (hv u hu).hasDerivWithinAt)
        (fun u hu => by simpa only [Real.norm_eq_abs] using hacc u hu) ht hs
  have habs (t : ℝ) (ht : t ∈ Icc 0 L) :=
    abs_velocity_lower_bound hh hL hA hδ hf hLip hmin ht
  have hsign := velocity_pos_of_abs_lower_bound (by linarith : 0 < L) hpos hf
    (fun u hu => (hv u hu).continuousAt.continuousWithinAt) habs horient
  intro t ht
  simpa only [abs_of_pos (hsign t ht)] using habs t ht





theorem scaled_velocity_lower_bound
    {f v acc : ℝ → ℝ} {L r ε h C δ : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hh : 0 < h) (hL : 2 * h ≤ L)
    (hf : ∀ u ∈ Icc 0 L, HasDerivAt f (v u) u)
    (hv : ∀ u ∈ Icc 0 L, HasDerivAt v (acc u) u)
    (hacc : ∀ u ∈ Icc 0 L, |acc u| ≤ δ)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L,
      a ≤ b → b - a ≤ r * Real.sqrt (1 + ε) * (|f b - f a| + C))
    (horient : f 0 < f L)
    (hpos : 0 < (r * Real.sqrt (1 + ε))⁻¹ - C / h - δ * h) :
    ∀ t ∈ Icc 0 L,
      (r * Real.sqrt (1 + ε))⁻¹ - C / h - δ * h ≤ v t := by
  have hA : 0 < r * Real.sqrt (1 + ε) := by
    exact mul_pos hr (Real.sqrt_pos.mpr (by linarith))
  have hL0 : 0 ≤ L := by linarith
  have hδ : 0 ≤ δ := (abs_nonneg (acc 0)).trans (hacc 0 ⟨le_rfl, hL0⟩)
  exact velocity_lower_bound hh hL hA hδ hf hv hacc hmin horient hpos

theorem scaled_velocity_close_to_unit
    {v : ℝ → ℝ} {L r α : ℝ}
    (hα : 0 ≤ α)
    (hlo : ∀ t ∈ Icc 0 L, 1 - α ≤ r * v t)
    (hhi : ∀ t ∈ Icc 0 L, r * v t ≤ 1) :
    ∀ t ∈ Icc 0 L, |r * v t - 1| ≤ α := by
  intro t ht
  have hlow := hlo t ht
  have hupp := hhi t ht
  apply abs_le.mpr
  constructor
  · linarith
  · linarith






theorem long_scaled_velocity_lower_bound
    {f v acc : ℝ → ℝ} {L r ε C δ : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hL : r / (100 * ε) < L)
    (hf : ∀ u ∈ Icc 0 L, HasDerivAt f (v u) u)
    (hv : ∀ u ∈ Icc 0 L, HasDerivAt v (acc u) u)
    (hacc : ∀ u ∈ Icc 0 L, |acc u| ≤ δ)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L,
      a ≤ b → b - a ≤ r * Real.sqrt (1 + ε) * (|f b - f a| + C))
    (horient : f 0 < f L)
    (hpos : 0 < (r * Real.sqrt (1 + ε))⁻¹ -
      C / (r / (200 * Real.sqrt ε)) - δ * (r / (200 * Real.sqrt ε))) :
    ∀ t ∈ Icc 0 L,
      (r * Real.sqrt (1 + ε))⁻¹ -
        C / (r / (200 * Real.sqrt ε)) - δ * (r / (200 * Real.sqrt ε)) ≤ v t := by
  have hsqrtpos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsqrt : ε ≤ Real.sqrt ε := by
    apply (Real.le_sqrt hε.le (by positivity)).mpr
    nlinarith [hε.le, hεhalf]
  have hwindow : 2 * (r / (200 * Real.sqrt ε)) ≤ L := by
    have hden₁ : 0 < 100 * Real.sqrt ε := by positivity
    have hden₂ : 0 < 100 * ε := by positivity
    have hcompare : r / (100 * Real.sqrt ε) ≤ r / (100 * ε) := by
      apply (div_le_div_iff₀ hden₁ hden₂).mpr
      nlinarith
    calc
      2 * (r / (200 * Real.sqrt ε)) = r / (100 * Real.sqrt ε) := by ring
      _ ≤ r / (100 * ε) := hcompare
      _ ≤ L := hL.le
  exact scaled_velocity_lower_bound hr hε hεhalf
    (by positivity) hwindow hf hv hacc hmin horient hpos

end PoincareConjecture.EpsilonNeck
