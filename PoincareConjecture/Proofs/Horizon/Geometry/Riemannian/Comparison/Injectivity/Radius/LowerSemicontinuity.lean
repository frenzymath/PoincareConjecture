import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.TotalInverse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.Nonconjugacy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity.FrozenMetric
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem chartGlobalExponential_center (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) :
    (fun v => g.chartGlobalExponential hc p (extChartAt (𝓡 n) p p, v)) =
      g.globalExponential hc p := by
  funext v
  let c := extChartAt (𝓡 n) p
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := p)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
  have hvec : mfderiv (𝓡 n) (𝓡 n) c.symm (c p) v = v :=
    congrArg (fun A => A v) hd
  change g.globalExponential hc (c.symm (c p))
    (mfderiv (𝓡 n) (𝓡 n) c.symm (c p) v) = g.globalExponential hc p v
  rw [hvec]
  exact congrArg (fun q => g.globalExponential hc q v) (c.left_inv (mem_extChartAt_source p))

theorem eventually_le_truncatedInjectivityRadius
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    {K C r : ℝ} (hK : 0 ≤ K) (hcurv : ∀ x : M, D.curvatureTensorNorm x ≤ K)
    (hC : 0 < C) (hCK : C ≤ Poincare.ODE.Jacobi.comparisonRadius K)
    (p : M) (hr : 0 < r) (hrρ : r < g.truncatedInjectivityRadius hc C p) :
    ∀ᶠ q in 𝓝 p, r ≤ g.truncatedInjectivityRadius hc C q := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  obtain ⟨s, hrs, hsρ⟩ := exists_between hrρ
  have hs : 0 < s := hr.trans hrs
  have hsC : s < C := hsρ.trans_le (g.truncatedInjectivityRadius_le hc hC.le p)
  obtain ⟨L, hL⟩ := g.exists_orthonormal_coordinate_frame p
  let A : Set E := L '' Metric.closedBall 0 s
  have hA : IsCompact A := (isCompact_closedBall (0 : E) s).image L.continuous
  have hcenter : (fun v => g.chartGlobalExponential hc p (c p, v)) =
      g.globalExponential hc p := g.chartGlobalExponential_center hc p
  have hnorm (v : E) : g.tangentNorm p v = ‖L.symm v‖ := by
    simpa only [L.apply_symm_apply] using g.tangentNorm_orthonormal_frame p L hL (L.symm v)
  have hAnorm (v : E) (hv : v ∈ A) : g.tangentNorm p v ≤ s := by
    obtain ⟨w, hw, rfl⟩ := hv
    rw [g.tangentNorm_orthonormal_frame p L hL]
    simpa using hw
  have hinj : InjOn (fun v => g.chartGlobalExponential hc p (c p, v)) A := by
    rw [hcenter]
    exact (g.injOn_globalExponential_truncatedInjectivityRadius hc hC.le p).mono
      (fun v hv => (hAnorm v hv).trans_lt hsρ)
  have hstable : ∀ᶠ x in 𝓝 (c p),
      InjOn (fun v => g.chartGlobalExponential hc p (x, v)) A := by
    apply Poincare.eventually_injOn_of_locally_injective_total_map hA hinj
    · intro v _
      exact (g.contMDiffAt_chartGlobalExponential hc p (z := (c p, v))
        (mem_extChartAt_target p)).continuousAt
    · intro v hv
      apply Poincare.exists_injOn_total_map_of_injective_fiber_mfderiv
        (g.contMDiffAt_chartGlobalExponential hc p (z := (c p, v))
          (mem_extChartAt_target p))
      rw [hcenter]
      exact g.injective_mfderiv_globalExponential_of_tangentNorm_lt D hc hK hcurv p
        ((hAnorm v hv).trans_lt (hsC.trans_le hCK))
  have hcSmooth : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (c p) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds (mem_extChartAt_target p))
  have hframe (v : E) : ‖L.symm v‖ =
      g.tangentNorm (c.symm (c p)) (mfderiv (𝓡 n) (𝓡 n) c.symm (c p) v) := by
    have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := p)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
    have hvec : mfderiv (𝓡 n) (𝓡 n) c.symm (c p) v = v :=
      congrArg (fun B => B v) hd
    rw [hvec]
    have hp : c.symm (c p) = p := c.left_inv (mem_extChartAt_source p)
    rw [hp]
    exact (hnorm v).symm
  let k : ℝ≥0 := ⟨s / r, (div_pos hs hr).le⟩
  have hk : 1 < k := (lt_div_iff₀ hr).mpr (by simpa using hrs)
  have hcomparison := g.eventually_pullbackNorm_comparison hcSmooth L.symm hframe hk
  have hnear : ∀ᶠ x in 𝓝 (c p), r ≤ g.truncatedInjectivityRadius hc C (c.symm x) := by
    filter_upwards [hstable, hcomparison,
      (isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds (mem_extChartAt_target p)]
      with x hxinj hxnorm hx
    apply g.le_truncatedInjectivityRadius hc (c.symm x) hr.le (hrs.le.trans hsC.le)
    let V : E →L[ℝ] E := mfderiv (𝓡 n) (𝓡 n) c (c.symm x)
    have hinverse (v : E) : mfderiv (𝓡 n) (𝓡 n) c.symm x (V v) = v := by
      have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓡 n) hx
      simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
      exact congrArg (fun B => B v) h
    have hmem (v : E) (hv : g.tangentNorm (c.symm x) v < r) : V v ∈ A := by
      refine ⟨L.symm (V v), ?_, L.apply_symm_apply _⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have h := (hxnorm (V v)).1
      rw [hinverse] at h
      have hlt := mul_lt_mul_of_pos_left hv (show 0 < (k : ℝ) from zero_lt_one.trans hk)
      have hkr : (k : ℝ) * r = s := div_mul_cancel₀ s hr.ne'
      exact (h.trans_lt (by simpa only [hkr] using hlt)).le
    intro v hv w hw heq
    have hco : V v = V w := hxinj (hmem v hv) (hmem w hw) (by
      change g.globalExponential hc (c.symm x)
        (mfderiv (𝓡 n) (𝓡 n) c.symm x (V v)) =
        g.globalExponential hc (c.symm x) (mfderiv (𝓡 n) (𝓡 n) c.symm x (V w))
      rwa [hinverse, hinverse])
    have h := congrArg (fun u => mfderiv (𝓡 n) (𝓡 n) c.symm x u) hco
    simpa only [hinverse] using h
  filter_upwards [(continuousAt_extChartAt p).preimage_mem_nhds hnear,
    (isOpen_extChartAt_source (I := 𝓡 n) p).mem_nhds (mem_extChartAt_source p)]
    with q hq hqc
  change r ≤ g.truncatedInjectivityRadius hc C (c.symm (c q)) at hq
  simpa only [c.left_inv hqc] using hq

theorem lowerSemicontinuous_truncatedInjectivityRadius
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    {K C : ℝ} (hK : 0 ≤ K) (hcurv : ∀ x : M, D.curvatureTensorNorm x ≤ K)
    (hC : 0 < C) (hCK : C ≤ Poincare.ODE.Jacobi.comparisonRadius K) :
    LowerSemicontinuous (g.truncatedInjectivityRadius hc C) := by
  intro p a ha
  obtain ⟨r, hr, hrρ⟩ := exists_between
    (max_lt ha (g.truncatedInjectivityRadius_pos hc hC p))
  have hrpos : 0 < r := (le_max_right a 0).trans_lt hr
  filter_upwards [g.eventually_le_truncatedInjectivityRadius D hc hK hcurv hC hCK p hrpos hrρ]
    with q hq
  exact ((le_max_left a 0).trans_lt hr).trans_le hq

end PoincareConjecture.RiemannianMetric
