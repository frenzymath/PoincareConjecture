import PoincareConjecture.Proofs.M35.RadialGauge.PicardIteration
import Mathlib.Analysis.Calculus.UniformLimitsDeriv









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge



theorem exists_weighted_geometric_limit {A F : Type*}
    [NormedAddCommGroup F] [CompleteSpace F]
    (w : A → ℝ) (hw : ∀ a, 1 ≤ w a) {f : ℕ → A → F} {C : ℝ}
    (hstep : ∀ k a, w a * ‖f (k + 1) a - f k a‖ ≤ C * (1 / 2 : ℝ) ^ k) :
    ∃ g : A → F, (∀ a, Tendsto (fun k => f k a) atTop (𝓝 (g a))) ∧
      (∀ k a, w a * ‖f k a - g a‖ ≤ 2 * C * (1 / 2 : ℝ) ^ k) ∧
      TendstoUniformly f g atTop := by
  have hw0 (a : A) : 0 < w a := lt_of_lt_of_le zero_lt_one (hw a)
  have hd (a : A) (k : ℕ) : dist (f k a) (f (k + 1) a) ≤
      (C / w a) * (1 / 2 : ℝ) ^ k := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (hw0 a), dist_eq_norm, norm_sub_rev, mul_comm]
    exact hstep k a
  choose g hg using fun a => cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 2 : ℝ) (C / w a) (by norm_num) (hd a))
  have htail (k : ℕ) (a : A) : w a * ‖f k a - g a‖ ≤ 2 * C * (1 / 2 : ℝ) ^ k := by
    have h := dist_le_of_le_geometric_of_tendsto (1 / 2 : ℝ) (C / w a)
      (by norm_num) (hd a) (hg a) k
    rw [dist_eq_norm] at h
    calc
      _ ≤ w a * ((C / w a) * (1 / 2 : ℝ) ^ k / (1 - 1 / 2)) :=
        mul_le_mul_of_nonneg_left h (hw0 a).le
      _ = _ := by field_simp [(hw0 a).ne']; ring
  refine ⟨g, hg, htail, Metric.tendstoUniformly_iff.mpr ?_⟩
  intro e he
  have hz : Tendsto (fun k : ℕ => 2 * C * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * C)
  filter_upwards [(tendsto_order.mp hz).2 e he] with k hk a
  rw [dist_eq_norm, norm_sub_rev]
  apply lt_of_le_of_lt _ hk
  have h := htail k a
  nlinarith [mul_nonneg (sub_nonneg.mpr (hw a)) (norm_nonneg (f k a - g a))]

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))




theorem exists_gaugePicard_c1_limit
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {eta T : ℝ}
    (hball : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖gaugePicard b G k t x‖ ≤ eta ∧
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x‖ ≤ eta)
    (hstep : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖gaugePicard b G (k + 1) t x - gaugePicard b G k t x‖ ≤
        eta * (1 / 2 : ℝ) ^ k ∧
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G (k + 1) t) x -
        fderiv ℝ (gaugePicard b G k t) x‖ ≤ eta * (1 / 2 : ℝ) ^ k)
    (hdiff : ∀ k t, t ∈ Icc 0 T → Differentiable ℝ (gaugePicard b G k t)) :
    ∃ u : ℝ → V → ℝ, (∀ t, t ∉ Icc 0 T → u t = 0) ∧ ∀ t, t ∈ Icc 0 T →
      Differentiable ℝ (u t) ∧
      TendstoUniformly (fun k => gaugePicard b G k t) (u t) atTop ∧
      TendstoUniformly (fun k => fderiv ℝ (gaugePicard b G k t)) (fderiv ℝ (u t)) atTop ∧
      (∀ x, (1 + ‖x‖) * ‖u t x‖ ≤ eta ∧ (1 + ‖x‖) * ‖fderiv ℝ (u t) x‖ ≤ eta) ∧
      ∀ k x, (1 + ‖x‖) * ‖gaugePicard b G k t x - u t x‖ ≤
          2 * eta * (1 / 2 : ℝ) ^ k ∧
        (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x - fderiv ℝ (u t) x‖ ≤
          2 * eta * (1 / 2 : ℝ) ^ k := by
  classical
  let J (k : ℕ) (p : Icc (0 : ℝ) T × V) : ℝ × (V →L[ℝ] ℝ) :=
    (gaugePicard b G k p.1 p.2, fderiv ℝ (gaugePicard b G k p.1) p.2)
  have hj (k : ℕ) (p : Icc (0 : ℝ) T × V) :
      (1 + ‖p.2‖) * ‖J (k + 1) p - J k p‖ ≤ eta * (1 / 2 : ℝ) ^ k := by
    rw [Prod.norm_def, mul_max_of_nonneg _ _ (by positivity)]
    exact max_le (hstep k p.1 p.1.property p.2).1 (hstep k p.1 p.1.property p.2).2
  obtain ⟨l, hl, htail, huni⟩ := exists_weighted_geometric_limit
    (fun p : Icc (0 : ℝ) T × V => 1 + ‖p.2‖) (fun p => by linarith [norm_nonneg p.2]) hj
  let u (t : ℝ) (x : V) := if ht : t ∈ Icc 0 T then (l (⟨t, ht⟩, x)).1 else 0
  have hu (t : ℝ) (ht : t ∈ Icc 0 T) : u t = fun x => (l (⟨t, ht⟩, x)).1 := by
    funext x
    simp only [u, dif_pos ht]
  refine ⟨u, ?_, ?_⟩
  · intro t ht
    funext x
    simp only [u, dif_neg ht, Pi.zero_apply]
  intro t ht
  have hu1 : TendstoUniformly (fun k x => gaugePicard b G k t x)
      (fun x => (l (⟨t, ht⟩, x)).1) atTop :=
    uniformContinuous_fst.comp_tendstoUniformly (huni.comp (fun x => (⟨t, ht⟩, x)))
  have hu2 : TendstoUniformly (fun k x => fderiv ℝ (gaugePicard b G k t) x)
      (fun x => (l (⟨t, ht⟩, x)).2) atTop :=
    uniformContinuous_snd.comp_tendstoUniformly (huni.comp (fun x => (⟨t, ht⟩, x)))
  have hderiv (x : V) : HasFDerivAt (u t) (l (⟨t, ht⟩, x)).2 x := by
    rw [hu t ht]
    exact hasFDerivAt_of_tendstoUniformly hu2
      (fun k y => (hdiff k t ht y).hasFDerivAt) (fun y => hu1.tendsto_at y) x
  have hdu : fderiv ℝ (u t) = fun x => (l (⟨t, ht⟩, x)).2 :=
    funext (fun x => (hderiv x).fderiv)
  refine ⟨fun x => (hderiv x).differentiableAt, ?_, ?_, ?_, ?_⟩
  · simpa only [hu t ht] using hu1
  · simpa only [hdu] using hu2
  · intro x
    rw [hdu, hu t ht]
    exact ⟨le_of_tendsto ((hu1.tendsto_at x).norm.const_mul (1 + ‖x‖))
        (Eventually.of_forall (fun k => (hball k t ht x).1)),
      le_of_tendsto ((hu2.tendsto_at x).norm.const_mul (1 + ‖x‖))
        (Eventually.of_forall (fun k => (hball k t ht x).2))⟩
  · intro k x
    rw [hdu, hu t ht]
    have h := htail k (⟨t, ht⟩, x)
    exact ⟨(mul_le_mul_of_nonneg_left
        (norm_fst_le (J k (⟨t, ht⟩, x) - l (⟨t, ht⟩, x))) (by positivity)).trans h,
      (mul_le_mul_of_nonneg_left
        (norm_snd_le (J k (⟨t, ht⟩, x) - l (⟨t, ht⟩, x))) (by positivity)).trans h⟩

end PoincareConjecture.M35.RadialGauge
