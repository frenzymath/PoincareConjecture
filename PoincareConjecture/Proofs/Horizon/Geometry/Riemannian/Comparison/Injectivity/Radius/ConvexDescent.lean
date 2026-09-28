import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.CutLoop
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.TwoGeodesics
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.ConvexLoop
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.MovingEndpoint
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.PrecompactData
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Descent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_stationary_radius_descent_of_convex
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (f : M → ℝ) (p : M) (hfp : f p = 0) (hfnonneg : ∀ z, 0 ≤ f z)
    (hconvex : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) → ConvexOn ℝ (Icc a b) (f ∘ curve))
    {K C m : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hCK : 2 * C ≤ Poincare.ODE.Jacobi.comparisonRadius K)
    (hcurv : ∀ z, D.curvatureTensorNorm z ≤ K)
    (hcore : ∀ z, f z = 0 → m ≤ g.truncatedInjectivityRadius hc C z)
    (x : M) (hx : g.truncatedInjectivityRadius hc C x < min m C) :
    ∃ y : M, f y ≤ f x ∧ ∃ H δ : ℝ, 0 < H ∧ 0 < δ ∧
      ∃ F : ℝ → ℝ, ∃ curve : ℝ → M,
        F 0 = g.truncatedInjectivityRadius hc C x ∧ HasDerivAt F 0 0 ∧
          ∀ s ∈ Ioo 0 δ, g.truncatedInjectivityRadius hc C (curve s) ≤ F s ∧
            f (curve s) ≤ f y - H * s := by
  let R := 2 * C
  have hR : 0 < R := by dsimp [R]; positivity
  have hCR : C < R := by dsimp [R]; linarith
  have hRK : R ≤ Poincare.ODE.Jacobi.comparisonRadius K := hCK
  have hxC := hx.trans_le (min_le_right _ _)
  have hxpos := g.truncatedInjectivityRadius_pos hc hC x
  obtain ⟨L, e, hL, he, he0, hed, hgeo, hgauss, hb, _, _, _⟩ :=
    g.exists_precompact_exponential_with_injectivity_data D x hR hK
      (g.isCompact_closure_ball_of_metricComplete hc x R) (fun z _ => hcurv z)
  have hbij (z) (hz : z ∈ Metric.ball 0 R) :
      Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e z) :=
    (hb z (by simpa only [min_eq_left hRK] using hz)).1
  obtain ⟨v, w, ev, ew, hv, hw, hvw, heq, hvs, hws, hsubv, hsubw,
      hev, hew, hvsmooth, hwsmooth, hvismooth, hwismooth, hvel⟩ :=
    g.exists_inverse_branches_at_truncatedInjectivityRadius hc x hC hCR hxC
      L e hL he0 hed (fun z hz => (hgeo z hz).1) he hbij hgauss
  have hvR := hsubv hvs
  have hwR := hsubw hws
  change (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) ev v v) =
    -(show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) ew w w) at hvel
  have hdv := (hev.eventuallyEq_of_mem (ev.open_source.mem_nhds hvs)).mfderiv_eq
    (I := 𝓡 n) (I' := 𝓡 n)
  have hdw := (hew.eventuallyEq_of_mem (ew.open_source.mem_nhds hws)).mfderiv_eq
    (I := 𝓡 n) (I' := 𝓡 n)
  have hyf : f (e v) ≤ f x := by
    rw [← he0]
    apply g.convex_value_le_center_of_opposite_radial_velocities f hconvex he
      (by dsimp [R]; rw [hv]; linarith) (by simpa using hwR)
      (hgeo v hvR).1 (hgeo w hwR).1 heq
    have h := hvel
    rw [hdv, hdw] at h
    exact h
  have hyradius : g.truncatedInjectivityRadius hc C (e v) ≤
      g.truncatedInjectivityRadius hc C x := by
    have h := g.truncatedInjectivityRadius_le_average_of_radial_collision hc hC.le x
      L e he0 hed he (fun z hz => (hgeo z hz).1) hgauss hvR hwR hvw heq
    rw [hv, hw] at h
    linarith
  have hypos : 0 < f (e v) := by
    apply lt_of_le_of_ne (hfnonneg _)
    intro hzero
    exact (not_le_of_gt (hx.trans_le (min_le_left _ _)))
      ((hcore _ hzero.symm).trans hyradius)
  obtain ⟨ε, hε, H, hH, curve, hcurve, hcurve0, _, _, hdescent, _⟩ :=
    g.exists_minimizing_geodesic_with_convex_descent hc f hconvex
      (show f p < f (e v) by simpa only [hfp] using hypos)
  have hγsmooth := hcurve.contMDiffAt
    (show (0 : ℝ) ∈ Ioo (-ε) (1 + ε) by constructor <;> linarith)
  have hyv : e v ∈ ev.target := by simpa only [hev hvs] using ev.map_source hvs
  have hyw : e v ∈ ew.target := by
    rw [heq]
    simpa only [hew hws] using ew.map_source hws
  have hiv : ev.symm (e v) = v := by rw [← hev hvs]; exact ev.left_inv hvs
  have hiw : ew.symm (e v) = w := by rw [heq, ← hew hws]; exact ew.left_inv hws
  have hgaussv (a : EuclideanSpace ℝ (Fin n)) :
      g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) ev v v)
        (mfderiv (𝓡 n) (𝓡 n) ev v a) = inner ℝ v a := by
    rw [hdv]
    exact hgauss v hvR a
  have hgaussw (a : EuclideanSpace ℝ (Fin n)) :
      g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) ew w w)
        (mfderiv (𝓡 n) (𝓡 n) ew w a) = inner ℝ w a := by
    rw [hdw, heq]
    exact hgauss w hwR a
  have havg := g.hasFDerivAt_average_inverse_radius_zero ev ew hvsmooth hwsmooth
    hvismooth hwismooth hyv hyw (by simpa only [hiv, hv] using hxpos)
    (by simp only [hiv, hiw, hv, hw])
    (by
      intro a
      have h := congrArg (fun z : EuclideanSpace ℝ (Fin n) =>
        g.inner (e v) (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) ev z z)
          (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) ev z a) = inner ℝ z a) hiv
      exact h.mpr (hgaussv a))
    (by
      intro a
      have h := congrArg (fun z : EuclideanSpace ℝ (Fin n) =>
        g.inner (e v) (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) ew z z)
          (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) ew z a) = inner ℝ z a) hiw
      exact h.mpr (hgaussw a))
    (by
      have hvd := congrArg (fun z : EuclideanSpace ℝ (Fin n) =>
        show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) ev z z) hiv
      have hwd := congrArg (fun z : EuclideanSpace ℝ (Fin n) =>
        -(show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) ew z z)) hiw.symm
      exact hvd.trans (hvel.trans hwd))
  let F : ℝ → ℝ := fun s => (‖ev.symm (curve s)‖ + ‖ew.symm (curve s)‖) / 2
  have hF0 : F 0 = g.truncatedInjectivityRadius hc C x := by
    dsimp [F]
    rw [hcurve0, hiv, hiw, hv, hw]
    ring
  have hFd : HasDerivAt F 0 0 := by
    have hchart := ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := 1)
      (show curve 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (e v)).source by
        rw [hcurve0]; exact mem_chart_source _ _)).comp 0 hγsmooth).mdifferentiableAt
      (by simp)
    have hcderiv := hchart.differentiableAt.hasDerivAt
    have havg' : HasFDerivAt
        (fun y => (‖ev.symm ((extChartAt (𝓡 n) (e v)).symm y)‖ +
          ‖ew.symm ((extChartAt (𝓡 n) (e v)).symm y)‖) / 2)
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (extChartAt (𝓡 n) (e v) (curve 0)) := by rw [hcurve0]; exact havg
    have hcomp := havg'.comp_hasDerivAt 0 hcderiv
    have hnear := hγsmooth.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (e v)).mem_nhds
        (show curve 0 ∈ (extChartAt (𝓡 n) (e v)).source by
          rw [hcurve0]; exact mem_extChartAt_source _))
    have heqnear : F =ᶠ[𝓝 0] (fun s =>
        (‖ev.symm ((extChartAt (𝓡 n) (e v)).symm (extChartAt (𝓡 n) (e v) (curve s)))‖ +
         ‖ew.symm ((extChartAt (𝓡 n) (e v)).symm (extChartAt (𝓡 n) (e v) (curve s)))‖) / 2) := by
      filter_upwards [hnear] with s hs
      simp only [(extChartAt (𝓡 n) (e v)).left_inv hs, F]
    simpa only [zero_apply] using hcomp.congr_of_eventuallyEq heqnear
  have hvcont : ContinuousAt (fun s => ev.symm (curve s)) 0 :=
    (ev.continuousAt_symm (by simpa only [hcurve0] using hyv)).comp hγsmooth.continuousAt
  have hwcont : ContinuousAt (fun s => ew.symm (curve s)) 0 :=
    (ew.continuousAt_symm (by simpa only [hcurve0] using hyw)).comp hγsmooth.continuousAt
  have hne0 : ev.symm (curve 0) ≠ ew.symm (curve 0) := by
    simpa only [hcurve0, hiv, hiw] using hvw
  have hvnear : ∀ᶠ s in 𝓝 (0 : ℝ), curve s ∈ ev.target :=
    hγsmooth.continuousAt.preimage_mem_nhds
      (ev.open_target.mem_nhds (by simpa only [hcurve0] using hyv))
  have hwnear : ∀ᶠ s in 𝓝 (0 : ℝ), curve s ∈ ew.target :=
    hγsmooth.continuousAt.preimage_mem_nhds
      (ew.open_target.mem_nhds (by simpa only [hcurve0] using hyw))
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), curve s ∈ ev.target ∧ curve s ∈ ew.target ∧
      ev.symm (curve s) ≠ ew.symm (curve s) := by
    filter_upwards [hvnear, hwnear, (hvcont.ne_iff_eventually_ne hwcont).mp hne0]
      with s hsv hsw hsne
    exact ⟨hsv, hsw, hsne⟩
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨e v, hyf, H, min δ 1, hH, lt_min hδ zero_lt_one, F, curve, hF0, hFd, ?_⟩
  intro s hs
  have hsδ : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
    exact hs.2.trans_le (min_le_left _ _)
  obtain ⟨hsv, hsw, hsne⟩ := hsmall hsδ
  have hsev : e (ev.symm (curve s)) = curve s :=
    (hev (ev.map_target hsv)).symm.trans (ev.right_inv hsv)
  have hsew : e (ew.symm (curve s)) = curve s :=
    (hew (ew.map_target hsw)).symm.trans (ew.right_inv hsw)
  refine ⟨?_, hdescent s ⟨hs.1.le, hs.2.le.trans (min_le_right _ _)⟩⟩
  have h := g.truncatedInjectivityRadius_le_average_of_radial_collision hc hC.le x
    L e he0 hed he (fun z hz => (hgeo z hz).1) hgauss
    (hsubv (ev.map_target hsv)) (hsubw (ew.map_target hsw)) hsne
    (hsev.trans hsew.symm)
  simpa only [hsev, F] using h

end PoincareConjecture.RiemannianMetric
