import PoincareConjecture.Proofs.M35.RadialGauge.PicardC2Limit










set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

noncomputable local instance m35PicardC3LimitLocal1 :
    NormedAddCommGroup (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35PicardC3LimitLocal2 :
    NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem gaugePicard_limit_contDiff_three
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ} {T C J : ℝ}
    (hu2 : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (u t))
    (hHess : ∀ t ∈ Icc 0 T,
      TendstoUniformly (fun k => fderiv ℝ (fderiv ℝ (gaugePicard b G k t)))
        (fderiv ℝ (fderiv ℝ (u t))) atTop)
    (hsmooth : ∀ k t, t ∈ Icc 0 T → ContDiff ℝ ∞ (gaugePicard b G k t))
    (hstep : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G (k + 1) t))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k t))) x‖ ≤ C * (1 / 2 : ℝ) ^ k)
    (hbound : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k t))) x‖ ≤ J) :
    ∀ t, t ∈ Icc 0 T → ContDiff ℝ 3 (u t) ∧
      TendstoUniformly (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k t))))
        (fderiv ℝ (fderiv ℝ (fderiv ℝ (u t)))) atTop ∧
      (∀ x, (1 + ‖x‖) *
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u t))) x‖ ≤ J) ∧
      ∀ k x, (1 + ‖x‖) *
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k t))) x -
          fderiv ℝ (fderiv ℝ (fderiv ℝ (u t))) x‖ ≤ 2 * C * (1 / 2 : ℝ) ^ k := by
  let K (k : ℕ) (p : Icc (0 : ℝ) T × V) :=
    fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k p.1.1))) p.2
  obtain ⟨l, hl, htail, huni⟩ := exists_weighted_geometric_limit
    (fun p : Icc (0 : ℝ) T × V => 1 + ‖p.2‖)
    (fun p => by linarith [norm_nonneg p.2])
    (f := K) (fun k p => hstep k p.1.1 p.1.2 p.2)
  intro t ht
  have hH_smooth (k : ℕ) :=
    (contDiff_infty_iff_fderiv.mp ((contDiff_infty_iff_fderiv.mp
      (hsmooth k t ht)).2)).2
  have hKuni : TendstoUniformly
      (fun k x => fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k t))) x)
      (fun x => l (⟨t, ht⟩, x)) atTop := huni.comp (fun x => (⟨t, ht⟩, x))
  have hKderiv (x : V) : HasFDerivAt (fderiv ℝ (fderiv ℝ (u t)))
      (l (⟨t, ht⟩, x)) x :=
    hasFDerivAt_of_tendstoUniformly hKuni
      (fun k y => ((hH_smooth k).differentiable (by simp) y).hasFDerivAt)
      (fun y => (hHess t ht).tendsto_at y) x
  have heq : fderiv ℝ (fderiv ℝ (fderiv ℝ (u t))) =
      fun x => l (⟨t, ht⟩, x) := funext (fun x => (hKderiv x).fderiv)
  have hKcont : Continuous (fun x => l (⟨t, ht⟩, x)) :=
    hKuni.continuous (Eventually.of_forall (fun k =>
      (contDiff_infty_iff_fderiv.mp (hH_smooth k)).2.continuous)).frequently
  have hH_c1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (u t))) :=
    contDiff_succ_iff_hasFDerivAt.mpr
      ⟨fun x => l (⟨t, ht⟩, x), contDiff_zero.mpr hKcont, hKderiv⟩
  have hgrad_c1 : ContDiff ℝ 1 (fderiv ℝ (u t)) := (hu2 t ht).fderiv_right (by norm_num)
  have hgrad_c2 : ContDiff ℝ 2 (fderiv ℝ (u t)) :=
    contDiff_succ_iff_hasFDerivAt.mpr
      ⟨fderiv ℝ (fderiv ℝ (u t)), hH_c1,
        fun x => (hgrad_c1.differentiable (by norm_num) x).hasFDerivAt⟩
  refine ⟨contDiff_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ (u t), hgrad_c2,
      fun x => ((hu2 t ht).differentiable (by norm_num) x).hasFDerivAt⟩, ?_, ?_, ?_⟩
  · simpa only [heq] using hKuni
  · intro x
    rw [heq]
    have hle (k : ℕ) : (1 + ‖x‖) * ‖l (⟨t, ht⟩, x)‖ ≤
        J + 2 * C * (1 / 2 : ℝ) ^ k := by
      have hb := hbound k t ht x
      have he := htail k (⟨t, ht⟩, x)
      have hn0 : ‖l (⟨t, ht⟩, x)‖ ≤
          ‖K k (⟨t, ht⟩, x)‖ + ‖l (⟨t, ht⟩, x) - K k (⟨t, ht⟩, x)‖ := by
        calc
          _ = ‖K k (⟨t, ht⟩, x) +
              (l (⟨t, ht⟩, x) - K k (⟨t, ht⟩, x))‖ := by congr 1; abel
          _ ≤ _ := norm_add_le (K k (⟨t, ht⟩, x))
            (l (⟨t, ht⟩, x) - K k (⟨t, ht⟩, x))
      have hn := mul_le_mul_of_nonneg_left hn0 (show 0 ≤ 1 + ‖x‖ by positivity)
      have he' : (1 + ‖x‖) * ‖l (⟨t, ht⟩, x) - K k (⟨t, ht⟩, x)‖ ≤
          2 * C * (1 / 2 : ℝ) ^ k := by
        have hnorm : ‖l (⟨t, ht⟩, x) - K k (⟨t, ht⟩, x)‖ =
            ‖K k (⟨t, ht⟩, x) - l (⟨t, ht⟩, x)‖ := by
          calc
            _ = ‖-(K k (⟨t, ht⟩, x) - l (⟨t, ht⟩, x))‖ := by congr 1; abel
            _ = _ := ContinuousLinearMap.opNorm_neg _
        rw [hnorm]
        exact he
      change (1 + ‖x‖) * ‖K k (⟨t, ht⟩, x)‖ ≤ J at hb
      linarith
    have hz : Tendsto (fun k : ℕ => J + 2 * C * (1 / 2 : ℝ) ^ k) atTop (𝓝 J) := by
      simpa only [one_div, one_mul, mul_zero, add_zero] using
        ((tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
            (2 * C)).const_add J
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hz (Eventually.of_forall hle)
  · intro k x
    rw [heq]
    exact htail k (⟨t, ht⟩, x)

end PoincareConjecture.M35.RadialGauge
