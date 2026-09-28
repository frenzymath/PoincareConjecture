import PoincareConjecture.Proofs.M35.RadialGauge.PicardHessianDifference
import PoincareConjecture.Proofs.M35.RadialGauge.PicardConvergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))




theorem gaugePicard_limit_contDiff_two
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ} {T C H : ℝ}
    (hu : ∀ t ∈ Icc 0 T, Differentiable ℝ (u t))
    (hgrad : ∀ t ∈ Icc 0 T,
      TendstoUniformly (fun k => fderiv ℝ (gaugePicard b G k t)) (fderiv ℝ (u t)) atTop)
    (hsmooth : ∀ k t, t ∈ Icc 0 T → ContDiff ℝ ∞ (gaugePicard b G k t))
    (hstep : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G (k + 1) t)) x -
        fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x‖ ≤ C * (1 / 2 : ℝ) ^ k)
    (hbound : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x‖ ≤ H) :
    ∀ t, t ∈ Icc 0 T → ContDiff ℝ 2 (u t) ∧
      TendstoUniformly (fun k => fderiv ℝ (fderiv ℝ (gaugePicard b G k t)))
        (fderiv ℝ (fderiv ℝ (u t))) atTop ∧
      (∀ x, (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ H) ∧
      ∀ k x, (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x -
        fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ 2 * C * (1 / 2 : ℝ) ^ k := by
  let J (k : ℕ) (p : Icc (0 : ℝ) T × V) :=
    fderiv ℝ (fderiv ℝ (gaugePicard b G k p.1.1)) p.2
  obtain ⟨l, hl, htail, huni⟩ := exists_weighted_geometric_limit
    (fun p : Icc (0 : ℝ) T × V => 1 + ‖p.2‖)
    (fun p => by linarith [norm_nonneg p.2])
    (f := J) (fun k p => hstep k p.1.1 p.1.2 p.2)
  intro t ht
  have hgrad_smooth (k : ℕ) := (contDiff_infty_iff_fderiv.mp (hsmooth k t ht)).2
  have hhess_smooth (k : ℕ) := (contDiff_infty_iff_fderiv.mp (hgrad_smooth k)).2
  have hHuni : TendstoUniformly (fun k x => fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x)
      (fun x => l (⟨t, ht⟩, x)) atTop := huni.comp (fun x => (⟨t, ht⟩, x))
  have hHderiv (x : V) : HasFDerivAt (fderiv ℝ (u t)) (l (⟨t, ht⟩, x)) x :=
    hasFDerivAt_of_tendstoUniformly hHuni
      (fun k y => ((hgrad_smooth k).differentiable (by simp) y).hasFDerivAt)
      (fun y => (hgrad t ht).tendsto_at y) x
  have heq : fderiv ℝ (fderiv ℝ (u t)) = fun x => l (⟨t, ht⟩, x) :=
    funext (fun x => (hHderiv x).fderiv)
  have hHcont : Continuous (fun x => l (⟨t, ht⟩, x)) :=
    hHuni.continuous (Eventually.of_forall (fun k => (hhess_smooth k).continuous)).frequently
  have hgrad_c1 : ContDiff ℝ 1 (fderiv ℝ (u t)) :=
    contDiff_succ_iff_hasFDerivAt.mpr
      ⟨fun x => l (⟨t, ht⟩, x), contDiff_zero.mpr hHcont, hHderiv⟩
  refine ⟨contDiff_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (u t), hgrad_c1, fun x => (hu t ht x).hasFDerivAt⟩, ?_, ?_, ?_⟩
  · simpa only [heq] using hHuni
  · intro x
    rw [heq]
    have hle (k : ℕ) : (1 + ‖x‖) * ‖l (⟨t, ht⟩, x)‖ ≤
        H + 2 * C * (1 / 2 : ℝ) ^ k := by
      have he := htail k (⟨t, ht⟩, x)
      have hb := hbound k t ht x
      have hn0 : ‖l (⟨t, ht⟩, x)‖ ≤
          ‖J k (⟨t, ht⟩, x)‖ + ‖l (⟨t, ht⟩, x) - J k (⟨t, ht⟩, x)‖ := by
        calc
          _ = ‖J k (⟨t, ht⟩, x) +
              (l (⟨t, ht⟩, x) - J k (⟨t, ht⟩, x))‖ := by congr 1; abel
          _ ≤ _ := norm_add_le (J k (⟨t, ht⟩, x))
            (l (⟨t, ht⟩, x) - J k (⟨t, ht⟩, x))
      have hn := mul_le_mul_of_nonneg_left hn0
        (show 0 ≤ 1 + ‖x‖ by positivity)
      change (1 + ‖x‖) * ‖J k (⟨t, ht⟩, x)‖ ≤ H at hb
      change (1 + ‖x‖) * ‖J k (⟨t, ht⟩, x) - l (⟨t, ht⟩, x)‖ ≤ _ at he
      have he' : (1 + ‖x‖) * ‖l (⟨t, ht⟩, x) - J k (⟨t, ht⟩, x)‖ ≤
          2 * C * (1 / 2 : ℝ) ^ k := by
        have hnorm : ‖l (⟨t, ht⟩, x) - J k (⟨t, ht⟩, x)‖ =
            ‖J k (⟨t, ht⟩, x) - l (⟨t, ht⟩, x)‖ := by
          calc
            _ = ‖-(J k (⟨t, ht⟩, x) - l (⟨t, ht⟩, x))‖ := by congr 1; abel
            _ = _ := ContinuousLinearMap.opNorm_neg _
        rw [hnorm]
        exact he
      linarith
    have hz : Tendsto (fun k : ℕ => H + 2 * C * (1 / 2 : ℝ) ^ k) atTop (𝓝 H) := by
      simpa only [one_div, one_mul, mul_zero, add_zero] using
        ((tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
            (2 * C)).const_add H
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hz
      (Eventually.of_forall hle)
  · intro k x
    rw [heq]
    exact htail k (⟨t, ht⟩, x)

end PoincareConjecture.M35.RadialGauge
