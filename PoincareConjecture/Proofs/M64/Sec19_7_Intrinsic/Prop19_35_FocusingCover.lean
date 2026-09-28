import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic














noncomputable section
set_option autoImplicit false

open Set Metric MeasureTheory
open scoped ENNReal

namespace PoincareConjecture




theorem m64Intrinsic_exists_measurable_focusing_cover
    {ι : Type*} (T : Set ι) (center radius : ι → ℝ)
    (ν : Measure ℝ) {A τ R : ℝ} (hτ : 3 < τ)
    (hradius : ∀ i ∈ T, 0 < radius i ∧ radius i ≤ R)
    (hfocus : ∀ i ∈ T,
      volume (closedBall (center i) (radius i)) ≤
        ENNReal.ofReal A * ν (closedBall (center i) (radius i))) :
    ∃ B : Set ℝ, MeasurableSet B ∧
      (∀ i ∈ T, closedBall (center i) (radius i) ⊆ B) ∧
      volume B ≤ ENNReal.ofReal (τ * A) * ν univ := by
  obtain ⟨S, hST, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      T center radius R (fun i hi => (hradius i hi).2) τ hτ
  have hcount : S.Countable := hdisj.countable_of_nonempty_interior (by
    intro i hi
    exact ⟨center i, ball_subset_interior_closedBall
      (mem_ball_self (hradius i (hST hi)).1)⟩)
  let := hcount.toEncodable
  let B : Set ℝ := ⋃ i : S, closedBall (center i) (τ * radius i)
  have hB : MeasurableSet B := MeasurableSet.iUnion (fun _ => measurableSet_closedBall)
  have hτpos : 0 ≤ τ := by linarith
  refine ⟨B, hB, ?_, ?_⟩
  · intro i hi x hx
    obtain ⟨j, hj, hsub⟩ := hcover i hi
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hsub hx⟩
  · calc
      volume B ≤ ∑' i : S, volume (closedBall (center i) (τ * radius i)) :=
        measure_iUnion_le _
      _ = ∑' i : S, ENNReal.ofReal τ *
          volume (closedBall (center i) (radius i)) := by
        congr 1
        ext i
        rw [Real.volume_closedBall, Real.volume_closedBall, ← ENNReal.ofReal_mul hτpos]
        congr 1
        ring
      _ ≤ ∑' i : S, ENNReal.ofReal τ *
          (ENNReal.ofReal A * ν (closedBall (center i) (radius i))) := by
        exact ENNReal.tsum_le_tsum (fun i =>
          mul_le_mul_right (hfocus i (hST i.2)) _)
      _ = ENNReal.ofReal (τ * A) *
          ∑' i : S, ν (closedBall (center i) (radius i)) := by
        rw [ENNReal.ofReal_mul hτpos, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_left, mul_assoc]
      _ ≤ ENNReal.ofReal (τ * A) * ν univ := by
        gcongr
        apply tsum_measure_le_measure_univ (fun _ => measurableSet_closedBall.nullMeasurableSet)
        intro i j hij
        exact (hdisj i.2 j.2 (fun h => hij (Subtype.ext h))).aedisjoint



theorem m64Intrinsic_exists_measurable_interval_cover
    (T : Set (ℝ × ℝ)) (ν : Measure ℝ) {A τ P : ℝ}
    (hτ : 3 < τ)
    (hT : ∀ p ∈ T, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ P)
    (hfocus : ∀ p ∈ T,
      ENNReal.ofReal (p.2 - p.1) ≤ ENNReal.ofReal A * ν (Icc p.1 p.2)) :
    ∃ B : Set ℝ, MeasurableSet B ∧
      (∀ p ∈ T, Icc p.1 p.2 ⊆ B) ∧
      volume B ≤ ENNReal.ofReal (τ * A) * ν univ := by
  have hball (p : ℝ × ℝ) :
      closedBall ((p.1 + p.2) / 2) ((p.2 - p.1) / 2) = Icc p.1 p.2 := by
    rw [Real.closedBall_eq_Icc]
    congr 1 <;> ring
  obtain ⟨B, hB, hcover, hbound⟩ := m64Intrinsic_exists_measurable_focusing_cover
    T (fun p => (p.1 + p.2) / 2) (fun p => (p.2 - p.1) / 2) ν hτ
    (R := P) (by
      intro p hp
      obtain ⟨ha, hab, hb⟩ := hT p hp
      constructor <;> linarith)
    (by intro p hp; simpa only [hball, Real.volume_Icc] using hfocus p hp)
  exact ⟨B, hB, fun p hp => by simpa only [hball] using hcover p hp, hbound⟩

end PoincareConjecture
