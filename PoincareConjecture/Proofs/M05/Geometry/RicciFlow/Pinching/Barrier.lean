import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Poincare.HamiltonIvey

open Set

noncomputable def logBarrier (t x : ℝ) : ℝ :=
  x * (Real.log x + Real.log (1 + t) - 3)

theorem continuous_logBarrier (t : ℝ) : Continuous (logBarrier t) := by
  convert! Real.continuous_mul_log.add
    (continuous_id.mul_const (Real.log (1 + t) - 3)) using 1
  ext x
  dsimp [logBarrier]
  ring

theorem strictConvexOn_logBarrier (t : ℝ) :
    StrictConvexOn ℝ (Ici 0) (logBarrier t) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have h := Real.strictConvexOn_mul_log.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul, logBarrier] at *
  nlinarith

theorem hasDerivAt_logBarrier (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (logBarrier t) (Real.log x + Real.log (1 + t) - 2) x := by
  convert! (Real.hasDerivAt_mul_log hx).add
    ((hasDerivAt_id x).mul_const (Real.log (1 + t) - 3)) using 1
  · ext y
    dsimp [logBarrier]
    ring
  · ring

theorem exists_base_cutoff :
    ∃ x : ℝ, Real.exp 2 < x ∧ logBarrier 0 x = -3 := by
  have he : (3 : ℝ) < Real.exp 2 := by
    convert Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num) using 1
    norm_num
  have hab : Real.exp (2 : ℝ) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
  have hmem : (-3 : ℝ) ∈ Icc (logBarrier 0 (Real.exp 2))
      (logBarrier 0 (Real.exp 3)) := by
    simp only [logBarrier, Real.log_exp, add_zero, Real.log_one]
    constructor <;> linarith
  obtain ⟨x, hx, hroot⟩ :=
    intermediate_value_Icc hab (continuous_logBarrier 0).continuousOn hmem
  refine ⟨x, ?_, hroot⟩
  have hne : Real.exp 2 ≠ x := by
    rintro rfl
    simp only [logBarrier, Real.log_exp, add_zero, Real.log_one] at hroot
    linarith
  exact lt_of_le_of_ne hx.1 hne

noncomputable def baseCutoff : ℝ := Classical.choose exists_base_cutoff

theorem baseCutoff_spec : Real.exp 2 < baseCutoff ∧ logBarrier 0 baseCutoff = -3 :=
  Classical.choose_spec exists_base_cutoff

theorem baseCutoff_pos : 0 < baseCutoff :=
  (Real.exp_pos 2).trans baseCutoff_spec.1

noncomputable def cutoff (t : ℝ) : ℝ := baseCutoff / (1 + t)

theorem logBarrier_div {t x : ℝ} (ht : 0 ≤ t) (hx : 0 < x) :
    logBarrier t (x / (1 + t)) = logBarrier 0 x / (1 + t) := by
  have hc : 0 < 1 + t := by linarith
  simp only [logBarrier, Real.log_div hx.ne' hc.ne', add_zero, Real.log_one]
  ring

theorem cutoff_pos {t : ℝ} (ht : 0 ≤ t) : 0 < cutoff t :=
  div_pos baseCutoff_pos (by linarith)

theorem cutoff_gt_first {t : ℝ} (ht : 0 ≤ t) : 1 / (1 + t) < cutoff t := by
  have hbase : (1 : ℝ) < baseCutoff := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith [baseCutoff_spec.1]
  exact (div_lt_div_iff_of_pos_right (by linarith : 0 < 1 + t)).mpr hbase

theorem logBarrier_cutoff {t : ℝ} (ht : 0 ≤ t) :
    logBarrier t (cutoff t) = -3 / (1 + t) := by
  rw [cutoff, logBarrier_div ht baseCutoff_pos, baseCutoff_spec.2]

theorem logBarrier_first {t : ℝ} (ht : 0 ≤ t) :
    logBarrier t (1 / (1 + t)) = -3 / (1 + t) := by
  rw [logBarrier_div ht (by norm_num : (0 : ℝ) < 1)]
  norm_num [logBarrier]

theorem cutoff_spec {t : ℝ} (ht : 0 ≤ t) :
    1 / (1 + t) < cutoff t ∧
      logBarrier t (cutoff t) = -3 / (1 + t) ∧
      ∀ x : ℝ, 1 / (1 + t) < x →
        logBarrier t x = -3 / (1 + t) → x = cutoff t := by
  refine ⟨cutoff_gt_first ht, logBarrier_cutoff ht, ?_⟩
  intro x hx hroot
  have hfirst : 0 < 1 / (1 + t) := by positivity
  have hc := cutoff_gt_first ht
  rcases lt_trichotomy x (cutoff t) with hlt | heq | hgt
  · have h := (strictConvexOn_logBarrier t).lt_on_openSegment
      hfirst.le (cutoff_pos ht).le hc.ne
      (show x ∈ openSegment ℝ (1 / (1 + t)) (cutoff t) by
        rw [openSegment_eq_Ioo hc]
        exact ⟨hx, hlt⟩)
    rw [hroot, logBarrier_first ht, logBarrier_cutoff ht, max_self] at h
    exact (lt_irrefl _ h).elim
  · exact heq
  · have h := (strictConvexOn_logBarrier t).lt_on_openSegment
      hfirst.le (hfirst.trans hx).le hx.ne
      (show cutoff t ∈ openSegment ℝ (1 / (1 + t)) x by
        rw [openSegment_eq_Ioo hx]
        exact ⟨hc, hgt⟩)
    rw [logBarrier_cutoff ht, logBarrier_first ht, hroot, max_self] at h
    exact (lt_irrefl _ h).elim

theorem strictMonoOn_logBarrier {t : ℝ} (ht : 0 ≤ t) :
    StrictMonoOn (logBarrier t) (Ici (cutoff t)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (continuous_logBarrier t).continuousOn
  intro x hx
  have hcut : cutoff t ≤ x := interior_subset hx
  have hxpos : 0 < x := (cutoff_pos ht).trans_le hcut
  rw [(hasDerivAt_logBarrier t hxpos.ne').deriv]
  have hlog : 2 < Real.log baseCutoff := by
    have := Real.log_lt_log (Real.exp_pos 2) baseCutoff_spec.1
    simpa only [Real.log_exp] using this
  have hle := Real.log_le_log (cutoff_pos ht) hcut
  rw [cutoff, Real.log_div baseCutoff_pos.ne' (by linarith : 1 + t ≠ 0)] at hle
  linarith

def scalarRegion (t : ℝ) : Set (ℝ × ℝ) :=
  {p | -3 / (1 + t) ≤ p.1 ∧ (cutoff t ≤ p.2 → logBarrier t p.2 ≤ p.1)}

noncomputable def clippedBarrier (t X : ℝ) : ℝ :=
  logBarrier t (max (cutoff t) X)

theorem monotone_clippedBarrier {t : ℝ} (ht : 0 ≤ t) :
    Monotone (clippedBarrier t) := by
  intro x y hxy
  exact (strictMonoOn_logBarrier ht).monotoneOn
    (mem_Ici.mpr (le_max_left _ _)) (mem_Ici.mpr (le_max_left _ _))
    (max_le_max_left _ hxy)

theorem convexOn_clippedBarrier {t : ℝ} (ht : 0 ≤ t) :
    ConvexOn ℝ univ (clippedBarrier t) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hcx := le_max_left (cutoff t) x
  have hcy := le_max_left (cutoff t) y
  have hcx' := le_max_right (cutoff t) x
  have hcy' := le_max_right (cutoff t) y
  have hmix : cutoff t ≤ a * max (cutoff t) x + b * max (cutoff t) y := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hcx ha)
      (mul_le_mul_of_nonneg_left hcy hb)
    rwa [← add_mul, hab, one_mul] at h
  have hmax : max (cutoff t) (a * x + b * y) ≤
      a * max (cutoff t) x + b * max (cutoff t) y := by
    apply max_le hmix
    exact add_le_add (mul_le_mul_of_nonneg_left hcx' ha)
      (mul_le_mul_of_nonneg_left hcy' hb)
  change logBarrier t (max (cutoff t) (a * x + b * y)) ≤
    a * logBarrier t (max (cutoff t) x) + b * logBarrier t (max (cutoff t) y)
  calc
    _ ≤ logBarrier t (a * max (cutoff t) x + b * max (cutoff t) y) :=
      (strictMonoOn_logBarrier ht).monotoneOn
        (mem_Ici.mpr (le_max_left _ _)) hmix hmax
    _ ≤ _ := (strictConvexOn_logBarrier t).convexOn.2
      ((cutoff_pos ht).le.trans hcx) ((cutoff_pos ht).le.trans hcy) ha hb hab

theorem mem_scalarRegion_iff {t S X : ℝ} (ht : 0 ≤ t) :
    (S, X) ∈ scalarRegion t ↔ clippedBarrier t X ≤ S := by
  change (-3 / (1 + t) ≤ S ∧ (cutoff t ≤ X → logBarrier t X ≤ S)) ↔
    logBarrier t (max (cutoff t) X) ≤ S
  by_cases hX : cutoff t ≤ X
  · rw [max_eq_right hX]
    constructor
    · exact fun h => h.2 hX
    · intro h
      refine ⟨?_, fun _ => h⟩
      rw [← logBarrier_cutoff ht]
      exact ((strictMonoOn_logBarrier ht).monotoneOn (mem_Ici.mpr (le_refl _)) hX hX).trans h
  · rw [max_eq_left (le_of_not_ge hX), logBarrier_cutoff ht]
    simp only [hX, false_implies, and_true]

theorem convex_scalarRegion {t : ℝ} (ht : 0 ≤ t) :
    Convex ℝ (scalarRegion t) := by
  intro p hp q hq a b ha hb hab
  rw [mem_scalarRegion_iff ht] at hp hq
  apply (mem_scalarRegion_iff ht).mpr
  change clippedBarrier t (a * p.2 + b * q.2) ≤ a * p.1 + b * q.1
  exact ((convexOn_clippedBarrier ht).2 (mem_univ _) (mem_univ _) ha hb hab).trans
    (add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb))

theorem scalarRegion_downward {t S X Y : ℝ} (ht : 0 ≤ t)
    (h : (S, X) ∈ scalarRegion t) (hYX : Y ≤ X) :
    (S, Y) ∈ scalarRegion t := by
  rw [mem_scalarRegion_iff ht] at h ⊢
  exact (monotone_clippedBarrier ht hYX).trans h

end Poincare.HamiltonIvey
