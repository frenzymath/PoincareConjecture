import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp









open Set Filter Metric
open scoped Topology

noncomputable section

namespace Poincare.MetricCurves

variable {X : Type*} [MetricSpace X]

private theorem exists_equal_step_chain
    (hsplit : ∀ x y : X, ∀ r : ℝ, 0 ≤ r → r ≤ dist x y →
      ∃ z : X, dist x z = r ∧ dist z y = dist x y - r)
    (n : ℕ) (x y : X) (r : ℝ) (hr : 0 ≤ r) (hxy : dist x y = n * r) :
    ∃ f : ℕ → X, f 0 = x ∧ f n = y ∧
      ∀ i ≤ n, ∀ j ≤ n, dist (f i) (f j) = |(i : ℝ) - j| * r := by
  induction n generalizing x y with
  | zero =>
    have h : x = y := dist_eq_zero.mp (by simpa using hxy)
    refine ⟨fun _ => x, rfl, h, ?_⟩
    intro i hi j hj
    have : i = 0 := Nat.eq_zero_of_le_zero hi
    have : j = 0 := Nat.eq_zero_of_le_zero hj
    simp_all
  | succ n ih =>
    obtain ⟨z, hxz, hzy⟩ := hsplit x y (n * r) (mul_nonneg (by positivity) hr)
      (by rw [hxy, Nat.cast_succ]; nlinarith)
    have hzy' : dist z y = r := by rw [hxy, Nat.cast_succ] at hzy; nlinarith
    obtain ⟨f, hf0, hfn, hf⟩ := ih x z hxz
    let g : ℕ → X := fun i => if i ≤ n then f i else y
    have hcross (i : ℕ) (hi : i ≤ n) :
        dist (f i) y = ((n + 1 : ℕ) - (i : ℝ)) * r := by
      have hin : (i : ℝ) ≤ n := by exact_mod_cast hi
      have hix := hf 0 (Nat.zero_le n) i hi
      have hiz := hf i hi n le_rfl
      simp only [hf0, Nat.cast_zero, zero_sub, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ i)] at hix
      rw [hfn, abs_of_nonpos (sub_nonpos.mpr hin)] at hiz
      have hu := dist_triangle (f i) z y
      have hl := dist_triangle x (f i) y
      rw [hiz, hzy'] at hu
      rw [hxy, hix, Nat.cast_succ] at hl
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith
    refine ⟨g, by simp [g, hf0], by simp [g], ?_⟩
    intro i hi j hj
    by_cases hin : i ≤ n <;> by_cases hjn : j ≤ n
    · simpa [g, hin, hjn] using hf i hin j hjn
    · have hj' : j = n + 1 := le_antisymm hj (Nat.succ_le_of_lt (Nat.lt_of_not_ge hjn))
      subst j
      have hir : (i : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hi
      simp only [g, if_pos hin, Nat.add_one_le_iff, lt_self_iff_false, if_false]
      rw [abs_of_nonpos (sub_nonpos.mpr hir), neg_sub]
      exact hcross i hin
    · have hi' : i = n + 1 := le_antisymm hi (Nat.succ_le_of_lt (Nat.lt_of_not_ge hin))
      subst i
      have hjr : (j : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hj
      simp only [g, if_pos hjn, Nat.add_one_le_iff, lt_self_iff_false, if_false]
      rw [abs_of_nonneg (sub_nonneg.mpr hjr), dist_comm]
      exact hcross j hjn
    · have hi' : i = n + 1 := le_antisymm hi (Nat.succ_le_of_lt (Nat.lt_of_not_ge hin))
      have hj' : j = n + 1 := le_antisymm hj (Nat.succ_le_of_lt (Nat.lt_of_not_ge hjn))
      simp [hi', hj']



theorem exists_metric_segment_of_splitting [ProperSpace X]
    (hsplit : ∀ x y : X, ∀ r : ℝ, 0 ≤ r → r ≤ dist x y →
      ∃ z : X, dist x z = r ∧ dist z y = dist x y - r)
    (x y : X) :
    ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y := by
  classical
  have hchains (n : ℕ) := exists_equal_step_chain hsplit (n + 1) x y
    (dist x y / (n + 1)) (div_nonneg dist_nonneg (by positivity))
    (by push_cast; field_simp)
  choose f hf0 hf1 hfdist using hchains
  let σ : ℕ → ℝ → X := fun n t => f n ⌊t * (n + 1)⌋₊
  have hindex (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ⌊t * (n + 1)⌋₊ ≤ n + 1 := by
    apply Nat.floor_le_of_le
    push_cast
    nlinarith [ht.2]
  have hσdist (n : ℕ) (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (σ n s) (σ n t) =
        |(⌊s * (n + 1)⌋₊ : ℝ) / (n + 1) -
          (⌊t * (n + 1)⌋₊ : ℝ) / (n + 1)| * dist x y := by
    change dist (f n _) (f n _) = _
    rw [hfdist n _ (hindex n s hs) _ (hindex n t ht)]
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    ring
  have hσ0 (n : ℕ) : σ n 0 = x := by simpa [σ] using hf0 n
  have hσ1 (n : ℕ) : σ n 1 = y := by
    simpa only [σ, one_mul, ← Nat.cast_add_one, Nat.floor_natCast] using hf1 n
  have hconf (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      σ n t ∈ closedBall x (dist x y) := by
    rw [mem_closedBall]
    conv_lhs => rw [← hσ0 n, hσdist n t 0 ht (by norm_num)]
    simp only [zero_mul, Nat.floor_zero, Nat.cast_zero, zero_div, sub_zero]
    rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
    apply mul_le_of_le_one_left dist_nonneg
    apply (div_le_one (by positivity)).mpr
    have := hindex n t ht
    exact_mod_cast this
  have hlim : ∀ t : ℝ, ∃ a : X, t ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => σ n t) (hyperfilter ℕ : Filter ℕ) (𝓝 a) := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · have hmem : closedBall x (dist x y) ∈ (hyperfilter ℕ).map (fun n => σ n t) := by
        change ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), σ n t ∈ closedBall x (dist x y)
        exact Eventually.of_forall (fun n => hconf n t ht)
      obtain ⟨a, _, ha⟩ := (isCompact_closedBall x (dist x y)).ultrafilter_le_nhds' _ hmem
      rw [Ultrafilter.coe_map] at ha
      exact ⟨a, fun _ => ha⟩
    · exact ⟨x, fun h => (ht h).elim⟩
  choose γ hγ using hlim
  have hfloor (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun n : ℕ => (⌊t * (n + 1)⌋₊ : ℝ) / (n + 1))
        (hyperfilter ℕ : Filter ℕ) (𝓝 t) := by
    exact (tendsto_nat_floor_mul_div_atTop ht).comp
      ((tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop (R := ℝ))).mono_left Nat.hyperfilter_le_atTop)
  refine ⟨γ, ?_, ?_, ?_⟩
  · exact tendsto_nhds_unique ((hγ 0 (by norm_num)).congr (fun n => hσ0 n))
      tendsto_const_nhds
  · exact tendsto_nhds_unique ((hγ 1 (by norm_num)).congr (fun n => hσ1 n))
      tendsto_const_nhds
  · intro s hs t ht
    have h₁ := (hγ s hs).dist (hγ t ht)
    have h₂ := ((hfloor s hs.1).sub (hfloor t ht.1)).abs.mul_const (dist x y)
    exact tendsto_nhds_unique h₁ (h₂.congr (fun n => (hσdist n s t hs ht).symm))

end Poincare.MetricCurves
