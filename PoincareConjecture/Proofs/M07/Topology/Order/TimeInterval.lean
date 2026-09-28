import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity












open Set Filter Topology

namespace Poincare.TimeInterval

private noncomputable def scale (n : ℕ) : ℝ := (n + 1 : ℝ) / (n + 2)

private theorem scale_pos (n : ℕ) : 0 < scale n := by
  unfold scale
  positivity

private theorem scale_lt_one (n : ℕ) : scale n < 1 := by
  unfold scale
  apply (div_lt_one (by positivity)).mpr
  linarith

private theorem scale_monotone : Monotone scale := by
  intro m n hmn
  unfold scale
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  nlinarith

private theorem scale_tendsto : Tendsto scale atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => (n + 1 : ℝ) / (n + 2)) atTop (𝓝 1)
  simpa only [one_mul, div_one, add_comm] using
    tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 2 1 (d := 1) one_ne_zero


def exhaustion (a b : ℝ) (n : ℕ) : Set ℝ := Icc (a * scale n) (b * scale n)

theorem isCompact_exhaustion (a b : ℝ) (n : ℕ) : IsCompact (exhaustion a b n) :=
  isCompact_Icc

theorem ordConnected_exhaustion (a b : ℝ) (n : ℕ) : (exhaustion a b n).OrdConnected :=
  ordConnected_Icc

theorem zero_mem_exhaustion {a b : ℝ} (ha : a < 0) (hb : 0 < b) (n : ℕ) :
    0 ∈ exhaustion a b n :=
  ⟨(mul_neg_of_neg_of_pos ha (scale_pos n)).le,
    (mul_pos hb (scale_pos n)).le⟩

theorem exhaustion_subset_Ioo {a b : ℝ} (ha : a < 0) (hb : 0 < b) (n : ℕ) :
    exhaustion a b n ⊆ Ioo a b := by
  apply Icc_subset_Ioo
  · simpa only [mul_one] using mul_lt_mul_of_neg_left (scale_lt_one n) ha
  · exact mul_lt_of_lt_one_right hb (scale_lt_one n)

theorem monotone_exhaustion {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    Monotone (exhaustion a b) := by
  intro m n hmn
  exact Icc_subset_Icc
    (mul_le_mul_of_nonpos_left (scale_monotone hmn) ha.le)
    (mul_le_mul_of_nonneg_left (scale_monotone hmn) hb.le)

theorem iUnion_interior_exhaustion {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    (⋃ n, interior (exhaustion a b n)) = Ioo a b := by
  apply subset_antisymm
  · exact iUnion_subset fun n => interior_subset.trans (exhaustion_subset_Ioo ha hb n)
  · intro x hx
    have hleft : Tendsto (fun n => a * scale n) atTop (𝓝 a) := by
      simpa only [mul_one] using scale_tendsto.const_mul a
    have hright : Tendsto (fun n => b * scale n) atTop (𝓝 b) := by
      simpa only [mul_one] using scale_tendsto.const_mul b
    obtain ⟨n, hn⟩ :=
      ((hleft.eventually_lt_const hx.1).and (hright.eventually_const_lt hx.2)).exists
    exact mem_iUnion.mpr ⟨n, by simpa only [exhaustion, interior_Icc, mem_Ioo] using hn⟩

theorem iUnion_exhaustion {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    (⋃ n, exhaustion a b n) = Ioo a b := by
  apply subset_antisymm (iUnion_subset fun n => exhaustion_subset_Ioo ha hb n)
  rw [← iUnion_interior_exhaustion ha hb]
  exact iUnion_mono fun _ => interior_subset



theorem exists_exhaustion_superset {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {K : Set ℝ} (hK : IsCompact K) (hKab : K ⊆ Ioo a b) :
    ∃ n, K ⊆ interior (exhaustion a b n) := by
  apply hK.elim_directed_cover (fun n => interior (exhaustion a b n))
    (fun _ => isOpen_interior)
  · rwa [iUnion_interior_exhaustion ha hb]
  · exact Monotone.directed_le fun _ _ h => interior_mono (monotone_exhaustion ha hb h)

end Poincare.TimeInterval
