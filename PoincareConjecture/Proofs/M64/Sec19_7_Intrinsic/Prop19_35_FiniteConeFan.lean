import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerConeArea
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory InnerProductGeometry
open scoped ENNReal Topology

namespace PoincareConjecture

private theorem complex_positive_cone_convex (x y : ℂ) :
    Convex ℝ {z : ℂ | ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ z = s • x + t • y} := by
  let L : (ℝ × ℝ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight x +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight y
  have heq : {z : ℂ | ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ z = s • x + t • y} =
      L '' (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    ext z
    constructor
    · rintro ⟨s, t, hs, ht, hz⟩
      exact ⟨(s, t), ⟨hs, ht⟩, hz.symm⟩
    · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, hz⟩
      exact ⟨s, t, hs, ht, hz.symm⟩
  rw [heq]
  exact ((convex_Ioi (0 : ℝ)).prod (convex_Ioi (0 : ℝ))).linear_image L.toLinearMap

theorem m64Intrinsic_complex_fan_angle_sum
    {I : Type*} [Fintype I] (x y : I → ℂ)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hangle : ∀ i, angle (x i) (y i) ∈ Ioo (0 : ℝ) Real.pi)
    (hpartition : ∀ᵐ z : ℂ, ∃! i, ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
      z = s • x i + t • y i) :
    (∑ i, angle (x i) (y i)) = 2 * Real.pi := by
  classical
  let C (i : I) : Set ℂ := {z | ‖z‖ < 1 ∧
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ z = s • x i + t • y i}
  have hconv (i : I) : Convex ℝ (C i) := by
    have hset : C i = Metric.ball (0 : ℂ) 1 ∩
        {z : ℂ | ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ z = s • x i + t • y i} := by
      ext z
      dsimp [C]
      change (‖z‖ < 1 ∧ ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
        z = s • x i + t • y i) ↔
        (z ∈ Metric.ball (0 : ℂ) 1 ∧ ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
          z = s • x i + t • y i)
      rw [Metric.mem_ball, dist_zero_right]
    rw [hset]
    exact (convex_ball (0 : ℂ) 1).inter (complex_positive_cone_convex (x i) (y i))
  have hdisj : Pairwise (fun i j => AEDisjoint volume (C i) (C j)) := by
    intro i j hij
    rw [AEDisjoint]
    apply measure_mono_null_ae
    · filter_upwards [hpartition] with z hz hboth
      obtain ⟨k, _, hk⟩ := hz
      exact (hij ((hk i hboth.1.2).trans (hk j hboth.2.2).symm)).elim
    · exact measure_empty
  have hcover : (⋃ i, C i) =ᵐ[volume] Metric.ball (0 : ℂ) 1 := by
    filter_upwards [hpartition] with z hz
    change (z ∈ ⋃ i, C i) = (z ∈ Metric.ball (0 : ℂ) 1)
    apply propext
    constructor
    · intro hzunion
      obtain ⟨i, hi⟩ := mem_iUnion.mp hzunion
      change z ∈ C i at hi
      rw [Metric.mem_ball, dist_zero_right]
      exact hi.1
    · intro hball
      rw [Metric.mem_ball, dist_zero_right] at hball
      obtain ⟨i, hi, _⟩ := hz
      exact mem_iUnion.mpr ⟨i, ⟨hball, hi⟩⟩
  have hsum : (∑ i, volume (C i)) = volume (Metric.ball (0 : ℂ) 1) := by
    calc
      _ = volume (⋃ i, C i) := by
        symm
        simpa only [tsum_fintype] using measure_iUnion₀ hdisj
          (fun i => (hconv i).nullMeasurableSet volume)
      _ = _ := measure_congr hcover
  have harea (i : I) : volume (C i) =
      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (angle (x i) (y i)) := by
    simpa only [one_pow] using m64Intrinsic_complex_corner_cone_volume
      (by norm_num : (0 : ℝ) < 1) (hx i) (hy i) (hangle i)
  simp_rw [harea] at hsum
  rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg
    (fun i _ => (hangle i).1.le), Complex.volume_ball] at hsum
  have hreal := congrArg ENNReal.toReal hsum
  have hsum_nonneg : 0 ≤ ∑ i, angle (x i) (y i) :=
    Finset.sum_nonneg (fun i _ => (hangle i).1.le)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.toReal_ofReal hsum_nonneg, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.coe_toReal] at hreal
  change (1 / 2 : ℝ) * ∑ i, angle (x i) (y i) = Real.pi at hreal
  linarith

end PoincareConjecture
