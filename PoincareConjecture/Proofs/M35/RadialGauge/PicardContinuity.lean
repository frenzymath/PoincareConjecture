import PoincareConjecture.Proofs.M35.RadialGauge.JointContinuity
import PoincareConjecture.Proofs.M35.RadialGauge.PicardRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem gaugePicard_slab_continuous
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T : ℝ}
    (hs : ∀ k,
      StronglyMeasurable (fun p : Icc 0 T × V =>
        gaugeSource (b p.1.1) (G p.1.1) (gaugePicard b G k p.1.1) p.2) ∧
      (∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (gaugeSource (b s) (G s) (gaugePicard b G k s))) ∧
      (∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (gaugeSource (b s) (G s) (gaugePicard b G k s)) x‖ ≤ C))
    (k : ℕ) :
    Continuous (fun p : Icc 0 T × V => gaugePicard b G k p.1.1 p.2) ∧
      Continuous (fun p : Icc 0 T × V => fderiv ℝ (gaugePicard b G k p.1.1) p.2) := by
  cases k with
  | zero =>
      constructor
      · exact continuous_const
      · simpa only [gaugePicard, fderiv_const_apply] using
          (continuous_const : Continuous (fun _ : Icc 0 T × V => (0 : V →L[ℝ] ℝ)))
  | succ k =>
      obtain ⟨C, hC⟩ := (hs k).2.2 0
      obtain ⟨D, hD⟩ := (hs k).2.2 1
      have hb (s : ℝ) (ht : s ∈ Icc 0 T) (x : V) :
          ‖gaugeSource (b s) (G s) (gaugePicard b G k s) x‖ ≤ C := by
        simpa only [norm_iteratedFDeriv_zero] using hC s ht x
      have hdb (s : ℝ) (ht : s ∈ Icc 0 T) (x : V) :
          ‖fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G k s)) x‖ ≤ D := by
        simpa only [norm_iteratedFDeriv_one] using hD s ht x
      exact ⟨heatDuhamel_slab_continuous (hs k).1
          (fun s ht => ((hs k).2.1 s ht).continuous) hb,
        heatDuhamel_fderiv_slab_continuous (hs k).1
          (fun s ht => ((hs k).2.1 s ht).of_le (by simp)) hb hdb⟩

theorem gaugePicard_limit_joint_continuous
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ} {T C : ℝ}
    (hc : ∀ k, Continuous (fun p : Icc 0 T × V => gaugePicard b G k p.1.1 p.2) ∧
      Continuous (fun p : Icc 0 T × V => fderiv ℝ (gaugePicard b G k p.1.1) p.2))
    (htail : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖gaugePicard b G k t x - u t x‖ ≤ C * (1 / 2 : ℝ) ^ k ∧
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x - fderiv ℝ (u t) x‖ ≤
        C * (1 / 2 : ℝ) ^ k) :
    Continuous (fun p : Icc 0 T × V => u p.1.1 p.2) ∧
      Continuous (fun p : Icc 0 T × V => fderiv ℝ (u p.1.1) p.2) := by
  let J (k : ℕ) (p : Icc 0 T × V) :=
    (gaugePicard b G k p.1.1 p.2, fderiv ℝ (gaugePicard b G k p.1.1) p.2)
  let U (p : Icc 0 T × V) := (u p.1.1 p.2, fderiv ℝ (u p.1.1) p.2)
  have huni : TendstoUniformly J U atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro e he
    have hz : Tendsto (fun k : ℕ => C * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul C
    filter_upwards [(tendsto_order.mp hz).2 e he] with k hk p
    rw [dist_eq_norm, norm_sub_rev, Prod.norm_def]
    apply max_lt
    · have h := (htail k p.1.1 p.1.2 p.2).1
      change ‖gaugePicard b G k p.1.1 p.2 - u p.1.1 p.2‖ < e
      nlinarith [mul_nonneg (norm_nonneg p.2)
        (norm_nonneg (gaugePicard b G k p.1.1 p.2 - u p.1.1 p.2))]
    · have h := (htail k p.1.1 p.1.2 p.2).2
      change ‖fderiv ℝ (gaugePicard b G k p.1.1) p.2 - fderiv ℝ (u p.1.1) p.2‖ < e
      nlinarith [mul_nonneg (norm_nonneg p.2)
        (norm_nonneg (fderiv ℝ (gaugePicard b G k p.1.1) p.2 - fderiv ℝ (u p.1.1) p.2))]
  have h : Continuous U := huni.continuous
    (Eventually.of_forall (fun k => (hc k).1.prodMk (hc k).2)).frequently
  exact ⟨h.fst, h.snd⟩

end PoincareConjecture.M35.RadialGauge
