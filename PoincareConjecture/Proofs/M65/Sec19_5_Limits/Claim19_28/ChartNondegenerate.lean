import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ChartLimit
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ProjectedSpeed

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

theorem m65ProjectedChart_metric_energy {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Icc a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m65FlowChartMetric F p (t, (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1)
      (deriv (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1) x)
      (deriv (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1) x) =
      curveSpeed P.flow c t x ^ 2 * (1 - m62Slope P c t x ^ 2) := by
  have hd : deriv (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1) x =
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1
        (curveVelocity (n := n) (fun y => (c y t).1) x) := by
    rw [m65ProjectedVelocity_eq_speed_smul P c hc ht, map_smul]
    exact (m65ProjectedCoordinates_hasDerivAt P c hc p ht hx).deriv
  rw [hd, m65FlowChartMetric_at_source F p t hx]
  rw [← M62.speed_sq F (fun y r => (c y r).1) t x]
  exact m65Projection_speed_sq P c hc ht x

theorem m65ProjectedChart_joint_metric_energy {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m65FlowChartMetric F p (t, (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1)
      (fderiv ℝ (m65ProjectedChartState P c p) (t, x) (0, 1)).2.1
      (fderiv ℝ (m65ProjectedChartState P c p) (t, x) (0, 1)).2.1 =
      curveSpeed P.flow c t x ^ 2 * (1 - m62Slope P c t x ^ 2) := by
  have hs := (m65ProjectedChartState_contDiffAt P c hc p ht hx).differentiableAt
    (by simp)
  have hd := (hs.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).hasDerivAt.deriv
  change deriv (fun y => m65ProjectedChartState P c p (t, y)) x =
    fderiv ℝ (m65ProjectedChartState P c p) (t, x) (0, 1) at hd
  rw [m65ProjectedChartState_spatial_deriv P c hc p ht hx] at hd
  rw [← hd]
  exact m65ProjectedChart_metric_energy P c hc p (Ioo_subset_Icc_self ht) hx

theorem m65ProjectedChart_limit_nondegenerate
    {circumference : ℕ → ℝ} (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k)) (p : M)
    {Ω : Set (ℝ × ℝ)}
    (hchart : ∀ k z, z ∈ Ω →
      (c k z.2 z.1).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    {Y : ℝ × ℝ → M65ProjectedChartStateSpace n}
    (hjet : ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (m65ProjectedChartState (P k) (c k) p))
      (iteratedFDeriv ℝ m Y) atTop K)
    {z : ℝ × ℝ} (hz : z ∈ Ω) (ht : z.1 ∈ Ioo a b)
    (hq : (Y z).2.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target)
    (hv : 0 < (Y z).2.2.1) (hu : (Y z).2.2.2 = 0) :
    m65FlowChartMetric F p (z.1, (Y z).2.1)
      (fderiv ℝ Y z (0, 1)).2.1 (fderiv ℝ Y z (0, 1)).2.1 = (Y z).2.2.1 ^ 2 ∧
      (fderiv ℝ Y z (0, 1)).2.1 ≠ 0 := by
  have h0raw := (hjet 0 {z} isCompact_singleton (singleton_subset_iff.mpr hz)).tendsto_at
    (mem_singleton z)
  have h0 : Tendsto (fun k => m65ProjectedChartState (P k) (c k) p z) atTop
      (𝓝 (Y z)) := by
    have h := ((continuous_eval_const (fun _ : Fin 0 => (0, 0))).tendsto _).comp h0raw
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using h
  have h1raw := (hjet 1 {z} isCompact_singleton (singleton_subset_iff.mpr hz)).tendsto_at
    (mem_singleton z)
  have h1 : Tendsto (fun k =>
      (fderiv ℝ (m65ProjectedChartState (P k) (c k) p) z (0, 1)).2.1) atTop
      (𝓝 (fderiv ℝ Y z (0, 1)).2.1) := by
    have h := ((continuous_eval_const (fun _ : Fin 1 => (0, 1))).tendsto _).comp h1raw
    simp only [Function.comp_def, iteratedFDeriv_one_apply] at h
    exact h.snd_nhds.fst_nhds
  have hqconv : Tendsto (fun k => (z.1,
      (chartAt (EuclideanSpace ℝ (Fin n)) p) (c k z.2 z.1).1)) atTop
      (𝓝 (z.1, (Y z).2.1)) := tendsto_const_nhds.prodMk_nhds h0.snd_nhds.fst_nhds
  have hgconv := ((m65FlowChartMetric_contDiffOn F p).continuousOn.continuousAt
    ((isOpen_Ioo.prod (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target).mem_nhds
      ⟨ht, hq⟩)).tendsto.comp hqconv
  have heval : Continuous (fun w :
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ×
        EuclideanSpace ℝ (Fin n) => w.1 w.2 w.2) := by fun_prop
  have hleft := heval.continuousAt.tendsto.comp (hgconv.prodMk_nhds h1)
  have hright : Tendsto (fun k => curveSpeed (P k).flow (c k) z.1 z.2 ^ 2 *
      (1 - m62Slope (P k) (c k) z.1 z.2 ^ 2)) atTop
      (𝓝 ((Y z).2.2.1 ^ 2 * (1 - (Y z).2.2.2 ^ 2))) :=
    (h0.snd_nhds.snd_nhds.fst_nhds.pow 2).mul
      (tendsto_const_nhds.sub (h0.snd_nhds.snd_nhds.snd_nhds.pow 2))
  have hsame (k : ℕ) := m65ProjectedChart_joint_metric_energy (P k) (c k) (hc k) p
    ht (hchart k z hz)
  have heq := tendsto_nhds_unique hleft (hright.congr fun k => (hsame k).symm)
  simp only [hu, zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_one] at heq
  refine ⟨heq, ?_⟩
  intro hzero
  simp only [hzero, map_zero] at heq
  exact (sq_pos_of_pos hv).ne' heq.symm

end PoincareConjecture
