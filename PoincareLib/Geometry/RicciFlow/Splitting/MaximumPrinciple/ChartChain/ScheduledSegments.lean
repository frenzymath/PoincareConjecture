import PoincareLib.Geometry.RicciFlow.Splitting.MaximumPrinciple.ChartChain.Geometry
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Smooth bounded-speed segments and positive elapsed times

The compact chart-ball subdivision is converted into affine coordinate paths.
Each path stays in the interior of the same compact chart ball and therefore
in the original open domain. Even a constant spatial piece receives positive
time; repeated subdivision cuts cause no zero-time comparisons.
-/

noncomputable section
open Set Metric
open scoped ContDiff

namespace PoincareMT.RicciFlow.Splitting.MaximumPrinciple.ChartChain

/-- Equal time cuts for a chain with `n` pieces. -/
def timeCut (a b : ℝ) (n k : ℕ) : ℝ := a + (k : ℝ) / n * (b - a)

/-- The first scheduled time is the allotted initial time. -/
theorem timeCut_zero (a b : ℝ) (n : ℕ) : timeCut a b n 0 = a := by
  simp [timeCut]

/-- The last scheduled time is the allotted terminal time. -/
theorem timeCut_last (a b : ℝ) {n : ℕ} (hn : 0 < n) : timeCut a b n n = b := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [timeCut, hn']

/-- Every piece gets exactly the same positive fraction of the allotted time. -/
theorem timeCut_sub (a b : ℝ) (n k : ℕ) :
    timeCut a b n (k + 1) - timeCut a b n k = (b - a) / n := by
  simp only [timeCut, Nat.cast_add, Nat.cast_one]
  ring

/-- Consecutive times are strictly increasing whenever the allotted interval is. -/
theorem timeCut_lt {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    timeCut a b n k < timeCut a b n (k + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := div_pos (sub_pos.mpr hab) hn'
  rw [← timeCut_sub a b n k] at h
  exact sub_pos.mp h

/-- Scheduled times stay in the prescribed closed time interval. -/
theorem timeCut_mem {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n)
    {k : ℕ} (hk : k ≤ n) : timeCut a b n k ∈ Icc a b := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hratio : (k : ℝ) / n ≤ 1 := (div_le_one hn').mpr hk'
  have hnonneg : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
  dsimp [timeCut]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg hnonneg (sub_nonneg.mpr hab.le))
  · nlinarith [mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr hab.le)]

/-- The positive elapsed times sum to exactly the prescribed time difference. -/
theorem timeCut_elapsed_sum (a b : ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ i : Fin n, (timeCut a b n (i + 1) - timeCut a b n i) = b - a := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [timeCut_sub, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The affine coordinate segment from `x` at time `a` to `y` at time `b`. -/
def coordinateSegment (x y : E) (a b t : ℝ) : E :=
  x + ((t - a) / (b - a)) • (y - x)

/-- Affine coordinate paths are globally smooth, including their endpoints. -/
theorem coordinateSegment_smooth (x y : E) (a b : ℝ) :
    ContDiff ℝ ∞ (coordinateSegment x y a b) :=
  contDiff_const.add (((contDiff_id.sub contDiff_const).div_const _).smul contDiff_const)

/-- The coordinate speed is the fixed displacement divided by the elapsed time. -/
theorem coordinateSegment_hasDerivAt (x y : E) (a b t : ℝ) :
    HasDerivAt (coordinateSegment x y a b) ((b - a)⁻¹ • (y - x)) t := by
  change HasDerivAt (fun s : ℝ => x + ((s - a) / (b - a)) • (y - x)) _ t
  simpa only [one_div, sub_zero, id_eq] using
    ((((hasDerivAt_id t).sub_const a).div_const (b - a)).smul_const (y - x)).const_add x

/-- A concrete finite uniform coordinate-speed bound on the entire real line. -/
theorem coordinateSegment_speed_bound (x y : E) (a b t : ℝ) :
    ‖deriv (coordinateSegment x y a b) t‖ ≤ ‖(b - a)⁻¹ • (y - x)‖ := by
  rw [(coordinateSegment_hasDerivAt x y a b t).deriv]

/-- The affine path starts at its prescribed coordinate. -/
theorem coordinateSegment_start (x y : E) (a b : ℝ) :
    coordinateSegment x y a b a = x := by simp [coordinateSegment]

/-- Positive elapsed time gives the prescribed terminal coordinate. -/
theorem coordinateSegment_end (x y : E) {a b : ℝ} (hab : a < b) :
    coordinateSegment x y a b b = y := by
  simp [coordinateSegment, ne_of_gt (sub_pos.mpr hab)]

/-- Convexity keeps the entire affine path in any coordinate ball containing
its endpoints. -/
theorem coordinateSegment_mem_ball {x y c : E} {r a b t : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ ball c r) (hab : a < b) (ht : t ∈ Icc a b) :
    coordinateSegment x y a b t ∈ ball c r := by
  have hd := sub_pos.mpr hab
  have h0 : 0 ≤ (t - a) / (b - a) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have h1 : (t - a) / (b - a) ≤ 1 := (div_le_one hd).mpr (by linarith [ht.2])
  have h := convex_ball c r hx hy (sub_nonneg.mpr h1) h0
    (show 1 - (t - a) / (b - a) + (t - a) / (b - a) = 1 by ring)
  convert h using 1
  dsimp [coordinateSegment]
  module

namespace ChartBall

/-- Straightening two core points gives the precise interior coordinate-path
hypothesis needed by the moving-bump theorem. -/
theorem segment_interior {U : Set M} (B : ChartBall I U) {p q : M}
    (hp : p ∈ B.core) (hq : q ∈ B.core) {a b : ℝ} (hab : a < b) :
    ∀ t ∈ Icc a b, ∃ x ∈ interior B.domain,
      extChartAt I B.center x =
        coordinateSegment (extChartAt I B.center p) (extChartAt I B.center q) a b t := by
  intro t ht
  have hseg := coordinateSegment_mem_ball hp.2 hq.2 hab ht
  refine ⟨(extChartAt I B.center).symm _,
    B.core_subset_interior (B.inverse_mem_core hseg), ?_⟩
  exact (extChartAt I B.center).right_inv (B.in_target (ball_subset_closedBall hseg))

end ChartBall

namespace Subdivision

variable {U : Set M} {p q : M} {γ : Path p q} (S : Subdivision (I := I) (U := U) γ)

/-- The left endpoint belongs to its piece's chart core. -/
theorem left_mem (i : Fin S.count) : γ (S.cut i) ∈ (S.ball i).core :=
  S.subordinate i _ ⟨le_rfl, S.monotone_cut (Nat.le_succ _)⟩

/-- The right endpoint belongs to its piece's chart core. -/
theorem right_mem (i : Fin S.count) : γ (S.cut (i + 1)) ∈ (S.ball i).core :=
  S.subordinate i _ ⟨S.monotone_cut (Nat.le_succ _), le_rfl⟩

/-- Adjacent compact chart domains share the same interior endpoint. -/
theorem overlap (i j : Fin S.count) (hij : (i : ℕ) + 1 = j) :
    γ (S.cut (i + 1)) ∈ interior (S.ball i).domain ∩ interior (S.ball j).domain := by
  refine ⟨(S.ball i).core_subset_interior (S.right_mem i), ?_⟩
  rw [hij]
  exact (S.ball j).core_subset_interior (S.left_mem j)

/-- The finitely many chart cores cover every point of the original path. -/
theorem range_subset_cores : range γ ⊆ ⋃ i : Fin S.count, (S.ball i).core := by
  have hcover : ∀ k : ℕ, k < S.count → ∀ t ∈ Icc (S.cut 0) (S.cut (k + 1)),
      ∃ i : Fin S.count, γ t ∈ (S.ball i).core := by
    intro k
    induction k with
    | zero =>
      intro hk t ht
      exact ⟨⟨0, hk⟩, S.subordinate ⟨0, hk⟩ t ht⟩
    | succ k ih =>
      intro hk t ht
      by_cases htk : t ≤ S.cut (k + 1)
      · exact ih (by omega) t ⟨ht.1, htk⟩
      · exact ⟨⟨k + 1, hk⟩, S.subordinate ⟨k + 1, hk⟩ t
          ⟨(lt_of_not_ge htk).le, ht.2⟩⟩
  rintro _ ⟨t, rfl⟩
  have hn : S.count - 1 + 1 = S.count := by have := S.count_pos; omega
  obtain ⟨i, hi⟩ := hcover (S.count - 1) (by have := S.count_pos; omega) t (by
    rw [hn, S.cut_zero, S.cut_last]
    exact ⟨unitInterval.nonneg t, unitInterval.le_one t⟩)
  exact mem_iUnion.mpr ⟨i, hi⟩

include S in
/-- An actual compact neighborhood of the whole path lies in the same domain.
It is the finite union of the constructed compact chart comparison domains. -/
theorem compact_neighborhood [FiniteDimensional ℝ E] :
    ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ range γ ⊆ interior K := by
  refine ⟨⋃ i : Fin S.count, (S.ball i).domain,
    isCompact_iUnion (fun i => (S.ball i).isCompact_domain),
    iUnion_subset (fun i => (S.ball i).domain_subset), ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (S.range_subset_cores hx)
  exact interior_mono (subset_iUnion (fun i : Fin S.count => (S.ball i).domain) i)
    ((S.ball i).core_subset_interior hi)

/-- Every scheduled piece has a smooth bounded-speed coordinate path in the
interior of its compact chart domain, for any positive allotted interval. -/
theorem scheduled_segment {a b : ℝ} (hab : a < b) (i : Fin S.count) :
    let l := timeCut a b S.count i
    let r := timeCut a b S.count (i + 1)
    ∃ c : ℝ → E, l < r ∧ ContDiff ℝ ∞ c ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖deriv c t‖ ≤ C) ∧
      c l = extChartAt I (S.ball i).center (γ (S.cut i)) ∧
      c r = extChartAt I (S.ball i).center (γ (S.cut (i + 1))) ∧
      ∀ t ∈ Icc l r, ∃ x ∈ interior (S.ball i).domain,
        extChartAt I (S.ball i).center x = c t := by
  dsimp only
  have hlt := timeCut_lt hab S.count_pos (i : ℕ)
  refine ⟨coordinateSegment _ _ _ _, hlt, coordinateSegment_smooth _ _ _ _,
    ⟨_, norm_nonneg _, coordinateSegment_speed_bound _ _ _ _⟩,
    coordinateSegment_start _ _ _ _, coordinateSegment_end _ _ hlt, ?_⟩
  exact (S.ball i).segment_interior (S.left_mem i) (S.right_mem i) hlt

end Subdivision

end PoincareMT.RicciFlow.Splitting.MaximumPrinciple.ChartChain

