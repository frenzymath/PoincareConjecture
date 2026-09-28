import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerNearLaplacianDecay
import Mathlib.Topology.UniformSpace.UniformApproximation











set_option autoImplicit false

open Set Filter
open scoped Topology

noncomputable section

namespace PoincareConjecture.M60




theorem suDyadic_holder_limit {X E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [CompleteSpace E] {S : Set X}
    {v : ℕ → X → E} {C : ℝ} (hC : 0 ≤ C)
    (hcont : ∀ j, ContinuousOn (v j) S)
    (hstep : ∀ j x, x ∈ S → dist (v j x) (v (j + 1) x) ≤ C * (1 / 2 : ℝ) ^ j)
    (hlip : ∀ j x, x ∈ S → ∀ y, y ∈ S →
      dist (v j x) (v j y) ≤ C * (8 : ℝ) ^ j * dist x y) :
    ∃ V : X → E, TendstoUniformlyOn v V atTop S ∧ ContinuousOn V S ∧
      (∀ j x, x ∈ S → dist (v j x) (V x) ≤ 2 * C * (1 / 2 : ℝ) ^ j) ∧
      ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1 →
        dist (V x) (V y) ≤ 10 * C * Real.sqrt (Real.sqrt (dist x y)) := by
  let V : X → E := fun x => limUnder atTop (fun j => v j x)
  have ht (x : X) (hx : x ∈ S) : Tendsto (fun j => v j x) atTop (𝓝 (V x)) :=
    (cauchySeq_of_le_geometric (1 / 2) C (by norm_num) (fun j => hstep j x hx)).tendsto_limUnder
  have herr (j : ℕ) (x : X) (hx : x ∈ S) :
      dist (v j x) (V x) ≤ 2 * C * (1 / 2 : ℝ) ^ j := by
    have h := dist_le_of_le_geometric_of_tendsto (1 / 2) C (by norm_num)
      (fun k => hstep k x hx) (ht x hx) j
    exact h.trans_eq (by ring)
  have hlim : Tendsto (fun j : ℕ => 2 * C * (1 / 2 : ℝ) ^ j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * C)
  have hunif : TendstoUniformlyOn v V atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hlim.eventually_lt_const hε] with j hj x hx
    have hh : dist (V x) (v j x) ≤ 2 * C * (1 / 2 : ℝ) ^ j := by
      simpa only [dist_comm] using herr j x hx
    exact hh.trans_lt hj
  refine ⟨V, hunif, hunif.continuousOn (Eventually.of_forall hcont).frequently, herr, ?_⟩
  intro x hx y hy hxy1
  by_cases hxy : x = y
  · subst y
    simp
  have hd : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near_of_lt_one hd hxy1
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1)
  have hpow : (8 : ℝ) ^ j * (1 / 16 : ℝ) ^ j = (1 / 2 : ℝ) ^ j := by
    rw [← mul_pow]
    norm_num
  have hbound : dist (V x) (V y) ≤ 5 * C * (1 / 2 : ℝ) ^ j := by
    have htri := dist_triangle4 (V x) (v j x) (v j y) (V y)
    have he1 := herr j x hx
    have he2 := herr j y hy
    have hl := (hlip j x hx y hy).trans
      (mul_le_mul_of_nonneg_left hjhi (by positivity : 0 ≤ C * (8 : ℝ) ^ j))
    rw [mul_assoc, hpow] at hl
    rw [dist_comm (V x) (v j x)] at htri
    linarith
  have hroot : (1 / 2 : ℝ) ^ (j + 1) < Real.sqrt (Real.sqrt (dist x y)) := by
    apply Real.lt_sqrt_of_sq_lt
    apply Real.lt_sqrt_of_sq_lt
    have heq : (((1 / 2 : ℝ) ^ (j + 1)) ^ 2) ^ 2 = (1 / 16 : ℝ) ^ (j + 1) := by
      calc
        _ = ((1 / 2 : ℝ) ^ 4) ^ (j + 1) := by
          simp only [← pow_mul]
          congr 1
          omega
        _ = _ := by norm_num
    exact heq.trans_lt hjlo
  have hlast : 5 * C * (1 / 2 : ℝ) ^ j ≤
      10 * C * Real.sqrt (Real.sqrt (dist x y)) := by
    have hh := mul_le_mul_of_nonneg_left hroot.le (show 0 ≤ 10 * C by positivity)
    rw [pow_succ] at hh
    nlinarith
  exact hbound.trans hlast

end PoincareConjecture.M60

end
