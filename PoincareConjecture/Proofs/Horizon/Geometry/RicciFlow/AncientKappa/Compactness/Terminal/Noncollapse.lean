import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.NormBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.MetricMonotonicity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

section Generic

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem terminal_tangentNorm_le_of_ricci_nonneg
    (F : RicciFlow n M (Iic 0)) {s : ℝ} (hs : s ≤ 0)
    (x : M) (v : TangentSpace (𝓡 n) x)
    (hRic : ∀ t ∈ Icc s 0, 0 ≤ (F.connection t).ricci x v v) :
    (F.metric 0).tangentNorm x v ≤ (F.metric s).tangentNorm x v := by
  have hd (t : ℝ) (ht : t ∈ interior (Icc s 0)) :
      HasDerivAt (fun u => (F.metric u).inner x v v)
        (-2 * (F.connection t).ricci x v v) t := by
    have ht0 : t < 0 := (show t ∈ Ioo s 0 from by simpa only [interior_Icc] using ht).2
    exact (F.equation t ht0.le x v v).hasDerivAt (Iic_mem_nhds ht0)
  have hanti : AntitoneOn (fun t => (F.metric t).inner x v v) (Icc s 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc s 0)
    · intro t ht
      exact (F.equation t ht.2 x v v).continuousWithinAt.mono (fun u hu => hu.2)
    · intro t ht
      exact (hd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t ht).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hRic t (interior_subset ht))
  exact Real.sqrt_le_sqrt (hanti ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs)

theorem ball_subset_terminal_ball_of_ricci_nonneg
    (F : RicciFlow n M (Iic 0)) {s : ℝ} (hs : s ≤ 0) (p : M) (r : ℝ)
    (hRic : ∀ t ∈ Icc s 0, ∀ x ∈ (F.metric s).ball p r,
      ∀ v : TangentSpace (𝓡 n) x, 0 ≤ (F.connection t).ricci x v v) :
    (F.metric s).ball p r ⊆ (F.metric 0).ball p r := by
  simpa only [one_mul] using RiemannianMetric.ball_subset_ball_of_tangentNorm_le
    (F.metric s) (F.metric 0) p r 1 zero_lt_one (by
      intro x hx v
      simpa only [one_mul] using F.terminal_tangentNorm_le_of_ricci_nonneg hs x v
        (fun t ht => hRic t ht x hx v))

end Generic

section ThreeDimensional

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [PreconnectedSpace M]

theorem earlier_ball_volume_le_exp_mul_terminal_ball
    (F : RicciFlow 3 M (Iic 0)) (p : M) {s B ρ r : ℝ}
    (hs : s ≤ 0) (hρr : ρ ≤ r)
    (hRic : ∀ t ∈ Icc s 0, ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      0 ≤ (F.connection t).ricci x v v)
    (hbound : ∀ t ∈ Icc s 0, ∀ x ∈ (F.metric 0).ball p r,
      (F.connection t).curvatureTensorNorm x ≤ B) :
    (F.metric s).volumeMeasure ((F.metric s).ball p ρ) ≤
      ENNReal.ofReal (Real.exp (27 * B * (-s))) ^ 3 *
        (F.metric 0).volumeMeasure ((F.metric 0).ball p r) := by
  let U := (F.metric 0).ball p r
  let c := Real.exp (27 * B * (-s))
  have hc : 0 < c := Real.exp_pos _
  have hzero : (0 : ℝ) ∈ Icc s 0 := ⟨hs, le_rfl⟩
  have hearly : s ∈ Icc s 0 := ⟨le_rfl, hs⟩
  have habsRic (t : ℝ) (ht : t ∈ Icc s 0) (x : M) (hx : x ∈ U)
      (v : TangentSpace (𝓡 3) x) :
      |(F.connection t).ricci x v v| ≤ (27 * B) * (F.metric t).inner x v v := by
    have h := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm x v
    have hv : 0 ≤ (F.metric t).inner x v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((F.metric t).pos x v hv).le
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at h
    norm_num at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound t ht x hx) (by norm_num)) hv)
  have hbackward (x : M) (hx : x ∈ U) (v : TangentSpace (𝓡 3) x) :
      (F.metric s).tangentNorm x v ≤ c * (F.metric 0).tangentNorm x v := by
    simpa only [sub_zero, abs_of_nonpos hs] using
      F.tangentNorm_le_exp_of_ricci_bound (convex_Icc s 0) (fun _ ht => ht.2)
        x v (27 * B) (fun t ht => habsRic t ht x hx v) hzero hearly
  have hU : IsOpen U := by
    let := (F.metric 0).toMetricSpace
    rw [show U = Metric.ball p r from ((F.metric 0).toMetricSpace_ball p r).symm]
    exact Metric.isOpen_ball
  have hvol := (F.metric 0).volumeMeasure_image_le_of_tangentNorm_le
    (F.metric s) (OpenPartialHomeomorph.refl M) hU (subset_univ U)
    contMDiffOn_id hc (by
      intro x hx v
      change (F.metric s).tangentNorm x (mfderiv (𝓡 3) (𝓡 3) id x v) ≤ _
      rw [mfderiv_id]
      exact hbackward x hx v)
    hU.measurableSet (Subset.refl U)
  change (F.metric s).volumeMeasure (id '' U) ≤ _ at hvol
  rw [image_id] at hvol
  apply (measure_mono ?_).trans hvol
  intro x hx
  exact (F.ball_subset_terminal_ball_of_ricci_nonneg hs p ρ
    (fun t ht y _ v => hRic t ht y v) hx).trans_le (ENNReal.ofReal_le_ofReal hρr)

theorem terminal_ball_volume_lower_bound_of_interior_noncollapse
    (F : RicciFlow 3 M (Iic 0)) (κ : ℝ)
    (hRic : ∀ t : ℝ, t ≤ 0 → ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      0 ≤ (F.connection t).ricci x v v)
    (hinterior : ∀ t : ℝ, t < 0 → ∀ p : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 3) ≤ (F.metric t).volumeMeasure ((F.metric t).ball p r))
    (p : M) {r : ℝ} (hr : 0 < r)
    (hcurv : ∀ s ∈ Ioc (-(r ^ 2)) 0, ∀ x ∈ (F.metric 0).ball p r,
      |(F.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (κ * r ^ 3) ≤ (F.metric 0).volumeMeasure ((F.metric 0).ball p r) := by
  have hsmall (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
      ENNReal.ofReal (κ * ρ ^ 3) ≤ (F.metric 0).volumeMeasure ((F.metric 0).ball p r) := by
    have hleft : ρ ^ 2 - r ^ 2 < 0 := by nlinarith
    have hradii : r⁻¹ ^ 2 ≤ ρ⁻¹ ^ 2 := by
      have hi := (inv_lt_inv₀ hr hρ).mpr hρr
      nlinarith [inv_pos.mpr hρ, inv_pos.mpr hr]
    have hearly (s : ℝ) (hs : s ∈ Ioo (ρ ^ 2 - r ^ 2) 0) :
        ENNReal.ofReal (κ * ρ ^ 3) ≤
          ENNReal.ofReal (Real.exp (27 * r⁻¹ ^ 2 * (-s))) ^ 3 *
            (F.metric 0).volumeMeasure ((F.metric 0).ball p r) := by
      have hball : (F.metric s).ball p ρ ⊆ (F.metric 0).ball p r := by
        intro x hx
        exact (F.ball_subset_terminal_ball_of_ricci_nonneg hs.2.le p ρ
          (fun t ht y _ v => hRic t ht.2 y v) hx).trans_le
            (ENNReal.ofReal_le_ofReal hρr.le)
      have hnoncollapse := hinterior s hs.2 p ρ hρ (by
        intro t ht x hx
        exact (hcurv t ⟨by linarith [ht.1, hs.1], ht.2.trans hs.2.le⟩ x
          (hball hx)).trans hradii)
      apply hnoncollapse.trans
      exact F.earlier_ball_volume_le_exp_mul_terminal_ball p hs.2.le hρr.le
        (fun t ht => hRic t ht.2) (by
          intro t ht x hx
          exact (le_abs_self _).trans (hcurv t ⟨by nlinarith [ht.1, hs.1], ht.2⟩ x hx))
    have hcoeff : Tendsto (fun s : ℝ =>
        ENNReal.ofReal (Real.exp (27 * r⁻¹ ^ 2 * (-s))) ^ 3)
        (𝓝[<] 0) (𝓝 (1 : ℝ≥0∞)) := by
      have hcont : Continuous (fun s : ℝ =>
          ENNReal.ofReal (Real.exp (27 * r⁻¹ ^ 2 * (-s)) ^ 3)) :=
        ENNReal.continuous_ofReal.comp
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id.neg)).pow 3)
      have h : Tendsto (fun s : ℝ =>
          ENNReal.ofReal (Real.exp (27 * r⁻¹ ^ 2 * (-s)) ^ 3))
          (𝓝[<] 0) (𝓝 (1 : ℝ≥0∞)) := by
        simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
      simpa only [ENNReal.ofReal_pow (Real.exp_nonneg _)] using h
    have hlim := ENNReal.Tendsto.mul_const
      (b := (F.metric 0).volumeMeasure ((F.metric 0).ball p r)) hcoeff (Or.inl one_ne_zero)
    simp only [one_mul] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hleft).filter_mono nhdsWithin_le_nhds] with s hs hsl
    exact hearly s ⟨hsl, hs⟩
  have hcoeff : Tendsto (fun ρ : ℝ => ENNReal.ofReal (κ * ρ ^ 3))
      (𝓝[<] r) (𝓝 (ENNReal.ofReal (κ * r ^ 3))) := by
    have hcont : Continuous (fun ρ : ℝ => ENNReal.ofReal (κ * ρ ^ 3)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow 3))
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hcoeff
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hr).filter_mono nhdsWithin_le_nhds] with ρ hρr hρ
  exact hsmall ρ hρ hρr

end ThreeDimensional
end PoincareConjecture.RicciFlow
