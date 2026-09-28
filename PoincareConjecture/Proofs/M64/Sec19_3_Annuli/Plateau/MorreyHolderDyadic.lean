import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerDyadicHolder












set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace PoincareConjecture



theorem m64Morrey_dyadic_holder_limit
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [CompleteSpace E]
    {S : Set X} {v : ℕ → X → E} {C alpha : ℝ} (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hcont : ∀ j, ContinuousOn (v j) S)
    (hstep : ∀ j x, x ∈ S →
      dist (v j x) (v (j + 1) x) ≤ C * ((1 / 16 : ℝ) ^ alpha) ^ j)
    (hlip : ∀ j x, x ∈ S → ∀ y, y ∈ S →
      dist (v j x) (v j y) ≤ C * (16 * (1 / 16 : ℝ) ^ alpha) ^ j * dist x y) :
    let q := (1 / 16 : ℝ) ^ alpha
    ∃ V : X → E, TendstoUniformlyOn v V atTop S ∧ ContinuousOn V S ∧
      (∀ j x, x ∈ S → dist (v j x) (V x) ≤ C / (1 - q) * q ^ j) ∧
      ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1 →
        dist (V x) (V y) ≤ (2 * C / (1 - q) + C) / q * (dist x y) ^ alpha := by
  intro q
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 16) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) halpha
  let V : X → E := fun x => limUnder atTop (fun j => v j x)
  have ht (x : X) (hx : x ∈ S) : Tendsto (fun j => v j x) atTop (𝓝 (V x)) :=
    (cauchySeq_of_le_geometric q C hq1 (fun j => hstep j x hx)).tendsto_limUnder
  have herr (j : ℕ) (x : X) (hx : x ∈ S) :
      dist (v j x) (V x) ≤ C / (1 - q) * q ^ j := by
    have h := dist_le_of_le_geometric_of_tendsto q C hq1
      (fun k => hstep k x hx) (ht x hx) j
    exact h.trans_eq (by ring)
  have hlim : Tendsto (fun j : ℕ => C / (1 - q) * q ^ j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul (C / (1 - q))
  have hunif : TendstoUniformlyOn v V atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    filter_upwards [hlim.eventually_lt_const hepsilon] with j hj x hx
    have hh : dist (V x) (v j x) ≤ C / (1 - q) * q ^ j := by
      simpa only [dist_comm] using herr j x hx
    exact hh.trans_lt hj
  refine ⟨V, hunif, hunif.continuousOn (Eventually.of_forall hcont).frequently, herr, ?_⟩
  intro x hx y hy hxy1
  by_cases hxy : x = y
  · subst y
    simp [Real.zero_rpow halpha.ne']
  have hd : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near_of_lt_one hd hxy1
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1)
  have hpow : (16 * q) ^ j * (1 / 16 : ℝ) ^ j = q ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  have hbound : dist (V x) (V y) ≤ (2 * C / (1 - q) + C) * q ^ j := by
    have htri := dist_triangle4 (V x) (v j x) (v j y) (V y)
    have he1 := herr j x hx
    have he2 := herr j y hy
    have hl := (hlip j x hx y hy).trans
      (mul_le_mul_of_nonneg_left hjhi (by positivity : 0 ≤ C * (16 * q) ^ j))
    rw [mul_assoc, hpow] at hl
    rw [dist_comm (V x) (v j x)] at htri
    exact (htri.trans (add_le_add (add_le_add he1 hl) he2)).trans_eq (by ring)
  have hroot : q ^ (j + 1) < (dist x y) ^ alpha := by
    have hh := Real.rpow_lt_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16) _)
      hjlo halpha
    simpa only [q, ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 16)] using hh
  have hqbound : q ^ j ≤ (dist x y) ^ alpha / q := by
    apply (le_div_iff₀ hq).mpr
    simpa only [pow_succ] using hroot.le
  exact hbound.trans ((mul_le_mul_of_nonneg_left hqbound
    (by positivity : 0 ≤ 2 * C / (1 - q) + C)).trans_eq (by ring))

end PoincareConjecture
