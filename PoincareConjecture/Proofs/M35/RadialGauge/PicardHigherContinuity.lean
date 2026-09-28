import PoincareConjecture.Proofs.M35.RadialGauge.PicardContinuity
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelThirdJets










set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

noncomputable local instance m35PicardHigherContinuityLocal1 :
    NormedAddCommGroup (V →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35PicardHigherContinuityLocal2 :
    NormedSpace ℝ (V →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

theorem heatDuhamel_hessian_slab_continuous
    {f : ℝ → V → F} {T : ℝ}
    (hfm : StronglyMeasurable (fun p : Icc 0 T × V => f p.1.1 p.2))
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (f s))
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ B) :
    Continuous (fun p : Icc 0 T × V => fderiv ℝ (fderiv ℝ (heatDuhamel f p.1.1)) p.2) := by
  obtain ⟨B1, hB1⟩ := hbound 1
  obtain ⟨B2, hB2⟩ := hbound 2
  have hc := heatDuhamel_fderiv_slab_continuous
    (spatial_fderiv_stronglyMeasurable (f := fun s : Icc 0 T => f s.1) hfm
      (fun s => (hf s.1 s.2).differentiable (by simp)))
    (fun s hs => ((contDiff_infty_iff_fderiv.mp (hf s hs)).2).of_le (by simp))
    (C := B1) (D := B2)
    (fun s hs x => by simpa only [norm_iteratedFDeriv_one] using hB1 s hs x)
    (fun s hs x => by
      simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] using hB2 s hs x)
  convert hc using 1
  funext p
  have hsub : Icc 0 p.1.1 ⊆ Icc 0 T := Icc_subset_Icc le_rfl p.1.2.2
  rw [heatDuhamel_fderiv_eq_of_slab p.1.2.1
    (hfm.comp_measurable (g := fun q : Icc 0 p.1.1 × V =>
      ((⟨q.1.1, hsub q.1.2⟩ : Icc 0 T), q.2)) (by fun_prop))
    (fun s hs => hf s (hsub hs))
    (fun j => by
      obtain ⟨B, hB⟩ := hbound j
      exact ⟨B, fun s hs => hB s (hsub hs)⟩)]

theorem heatDuhamel_third_derivative_slab_continuous
    {f : ℝ → V → F} {T : ℝ}
    (hfm : StronglyMeasurable (fun p : Icc 0 T × V => f p.1.1 p.2))
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (f s))
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ B) :
    Continuous (fun p : Icc 0 T × V =>
      fderiv ℝ (fderiv ℝ (fderiv ℝ (heatDuhamel f p.1.1))) p.2) := by
  have hc := heatDuhamel_hessian_slab_continuous
    (spatial_fderiv_stronglyMeasurable (f := fun s : Icc 0 T => f s.1) hfm
      (fun s => (hf s.1 s.2).differentiable (by simp)))
    (fun s hs => (contDiff_infty_iff_fderiv.mp (hf s hs)).2)
    (fun j => by
      obtain ⟨B, hB⟩ := hbound (j + 1)
      exact ⟨B, fun s hs x => by rw [norm_iteratedFDeriv_fderiv]; exact hB s hs x⟩)
  convert hc using 1
  funext p
  have hsub : Icc 0 p.1.1 ⊆ Icc 0 T := Icc_subset_Icc le_rfl p.1.2.2
  rw [heatDuhamel_fderiv_eq_of_slab p.1.2.1
    (hfm.comp_measurable (g := fun q : Icc 0 p.1.1 × V =>
      ((⟨q.1.1, hsub q.1.2⟩ : Icc 0 T), q.2)) (by fun_prop))
    (fun s hs => hf s (hsub hs))
    (fun j => by
      obtain ⟨B, hB⟩ := hbound j
      exact ⟨B, fun s hs => hB s (hsub hs)⟩)]

omit [NormedSpace ℝ F] in
theorem continuous_of_weighted_geometric_tail
    {A : Type*} [TopologicalSpace A] {f : ℕ → A → V → F} {u : A → V → F} {C : ℝ}
    (hc : ∀ k, Continuous (fun p : A × V => f k p.1 p.2))
    (htail : ∀ k a x, (1 + ‖x‖) * ‖f k a x - u a x‖ ≤ C * (1 / 2 : ℝ) ^ k) :
    Continuous (fun p : A × V => u p.1 p.2) := by
  have huni : TendstoUniformly (fun k (p : A × V) => f k p.1 p.2)
      (fun p : A × V => u p.1 p.2) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro e he
    have hz : Tendsto (fun k : ℕ => C * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul C
    filter_upwards [(tendsto_order.mp hz).2 e he] with k hk p
    rw [dist_eq_norm, norm_sub_rev]
    have h := htail k p.1 p.2
    nlinarith only [h, hk, mul_nonneg (norm_nonneg p.2) (norm_nonneg (f k p.1 p.2 - u p.1 p.2))]
  exact huni.continuous (Eventually.of_forall hc).frequently

noncomputable local instance m35PicardHigherContinuityLocal3 :
    NormedAddCommGroup (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35PicardHigherContinuityLocal4 :
    NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
noncomputable local instance m35PicardHigherContinuityLocal5 :
    NormedAddCommGroup (V →L[ℝ] (V →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35PicardHigherContinuityLocal6 :
    NormedSpace ℝ (V →L[ℝ] (V →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem gaugePicard_slab_higher_continuous
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T : ℝ}
    (hs : ∀ k,
      StronglyMeasurable (fun p : Icc 0 T × V =>
        gaugeSource (b p.1.1) (G p.1.1) (gaugePicard b G k p.1.1) p.2) ∧
      (∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (gaugeSource (b s) (G s) (gaugePicard b G k s))) ∧
      (∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (gaugeSource (b s) (G s) (gaugePicard b G k s)) x‖ ≤ C))
    (k : ℕ) :
    Continuous (fun p : Icc 0 T × V => fderiv ℝ (fderiv ℝ (gaugePicard b G k p.1.1)) p.2) ∧
      Continuous (fun p : Icc 0 T × V =>
        fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k p.1.1))) p.2) := by
  cases k with
  | zero =>
      constructor
      · simpa only [gaugePicard, fderiv_fun_const, fderiv_zero, Pi.zero_apply] using
          (continuous_const : Continuous (fun _ : Icc 0 T × V => (0 : V →L[ℝ] (V →L[ℝ] ℝ))))
      · simpa only [gaugePicard, fderiv_fun_const, fderiv_zero, Pi.zero_apply] using
          (continuous_const : Continuous (fun _ : Icc 0 T × V =>
            (0 : V →L[ℝ] (V →L[ℝ] (V →L[ℝ] ℝ)))))
  | succ k =>
      exact ⟨heatDuhamel_hessian_slab_continuous (hs k).1 (hs k).2.1 (hs k).2.2,
        heatDuhamel_third_derivative_slab_continuous (hs k).1 (hs k).2.1 (hs k).2.2⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem gaugePicard_limit_joint_higher_continuous
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ} {T C2 C3 : ℝ}
    (hc : ∀ k,
      Continuous (fun p : Icc 0 T × V => fderiv ℝ (fderiv ℝ (gaugePicard b G k p.1.1)) p.2) ∧
      Continuous (fun p : Icc 0 T × V =>
        fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k p.1.1))) p.2))
    (htail2 : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x -
        fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C2 * (1 / 2 : ℝ) ^ k)
    (htail3 : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k t))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (u t))) x‖ ≤ C3 * (1 / 2 : ℝ) ^ k) :
    Continuous (fun p : Icc 0 T × V => fderiv ℝ (fderiv ℝ (u p.1.1)) p.2) ∧
      Continuous (fun p : Icc 0 T × V => fderiv ℝ (fderiv ℝ (fderiv ℝ (u p.1.1))) p.2) := by
  exact ⟨continuous_of_weighted_geometric_tail (fun k => (hc k).1)
      (fun k (t : Icc 0 T) => htail2 k t.1 t.2),
    continuous_of_weighted_geometric_tail (fun k => (hc k).2)
      (fun k (t : Icc 0 T) => htail3 k t.1 t.2)⟩

end PoincareConjecture.M35.RadialGauge
