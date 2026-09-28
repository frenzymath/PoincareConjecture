import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.SmoothFlow
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.CoordinateField
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.MetricVariation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [T3Space M] in
private theorem chartCoefficients_apply_chartDifferential
    (g : RiemannianMetric n M) (a : M) {y : M}
    (hy : y ∈ (extChartAt (𝓡 n) a).source) (v w : TangentSpace (𝓡 n) y) :
    g.pullbackCoefficients (extChartAt (𝓡 n) a).symm (extChartAt (𝓡 n) a y)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) y v)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) y w) = g.inner y v w := by
  have hid := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 n) hy
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hid
  have hidv := congrArg (fun L => L v) hid
  have hidw := congrArg (fun L => L w) hid
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hidv hidw
  change g.inner ((extChartAt (𝓡 n) a).symm (extChartAt (𝓡 n) a y))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (extChartAt (𝓡 n) a y)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) y v))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (extChartAt (𝓡 n) a y)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) y w)) = _
  rw [hidv, hidw]
  exact congrArg (fun z => g.inner z v w) ((extChartAt (𝓡 n) a).left_inv hy)

omit [T3Space M] in
private theorem metric_pullback_in_charts
    {F : M → M} {x : M} (hF : ContMDiffAt (𝓡 n) (𝓡 n) ∞ F x)
    (a : M) (ha : F x ∈ (extChartAt (𝓡 n) a).source)
    (v w : TangentSpace (𝓡 n) x) :
    let c := extChartAt (𝓡 n) a
    let d := extChartAt (𝓡 n) x
    g.pullbackCoefficients c.symm (c (F x))
      (fderiv ℝ (c ∘ F ∘ d.symm) (d x) v)
      (fderiv ℝ (c ∘ F ∘ d.symm) (d x) w) =
        g.inner (F x) (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w) := by
  let c := extChartAt (𝓡 n) a
  let d := extChartAt (𝓡 n) x
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c (F x) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using ha)
  have hd : MDifferentiableAt (𝓡 n) (𝓡 n) d.symm (d x) :=
    ((contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 n) (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
        (extChartAt_target_mem_nhds x)).mdifferentiableAt (by simp)
  have hdid : mfderiv (𝓡 n) (𝓡 n) d.symm (d x) = ContinuousLinearMap.id ℝ _ := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
  have hFd : MDifferentiableAt (𝓡 n) (𝓡 n) F (d.symm (d x)) := by
    simpa only [d, extChartAt_to_inv] using hF.mdifferentiableAt (by simp)
  have hcd : MDifferentiableAt (𝓡 n) (𝓡 n) c (F (d.symm (d x))) := by
    simpa only [d, extChartAt_to_inv] using hc
  have hderiv := mfderiv_comp (d x) hcd (hFd.comp (d x) hd)
  rw [mfderiv_comp (d x) hFd hd, hdid, ContinuousLinearMap.comp_id] at hderiv
  rw [mfderiv_eq_fderiv] at hderiv
  change fderiv ℝ (c ∘ F ∘ d.symm) (d x) =
    (mfderiv (𝓡 n) (𝓡 n) c (F (d.symm (d x)))).comp
      (mfderiv (𝓡 n) (𝓡 n) F (d.symm (d x))) at hderiv
  rw [show d.symm (d x) = x from extChartAt_to_inv x] at hderiv
  dsimp only
  rw [hderiv]
  exact chartCoefficients_apply_chartDifferential g a ha _ _



theorem hasDerivAt_gradientFlow_metric_pairing_eq_zero
    {D : LeviCivitaData g} {f : M → ℝ} {Φ : ℝ → M → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hzero : HasZeroHessian D f)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (fun z : ℝ × M => Φ z.1 z.2))
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient f))
    (x : M) (v w : TangentSpace (𝓡 n) x) (t : ℝ) :
    HasDerivAt (fun s => g.inner (Φ s x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ s) x w)) 0 t := by
  let c := extChartAt (𝓡 n) (Φ t x)
  let d := extChartAt (𝓡 n) x
  let q : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => c (Φ z.1 (d.symm z.2))
  let G := mpullback (𝓡 n) (𝓡 n) c.symm (D.gradient f)
  let B := g.pullbackCoefficients c.symm
  have hdx : d.symm (d x) = x := extChartAt_to_inv x
  have hqt : q (t, d x) = c (Φ t x) := by simp only [q, hdx]
  have hct : q (t, d x) ∈ c.target := by rw [hqt]; exact mem_extChartAt_target _
  have hd : ContMDiffAt (𝓡 n) (𝓡 n) ∞ d.symm (d x) :=
    (contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 n) (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt (extChartAt_target_mem_nhds x)
  have hfamily : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => Φ z.1 (d.symm z.2)) (t, d x) := by
    have hp : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (z.1, d.symm z.2)) (t, d x) :=
      (contMDiffAt_iff_contDiffAt.mpr contDiffAt_fst).prodMk
        (hd.comp (t, d x) (contMDiffAt_iff_contDiffAt.mpr contDiffAt_snd))
    exact (hs _).comp (t, d x) hp
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (Φ t (d.symm (d x))) := by
    rw [hdx]
    exact contMDiffAt_extChartAt' (mem_chart_source _ _)
  have hq : ContDiffAt ℝ ∞ q (t, d x) :=
    contMDiffAt_iff_contDiffAt.mp (hc.comp (t, d x) hfamily)
  have hG : DifferentiableAt ℝ G (q (t, d x)) :=
    (contDiffAt_mpullback_gradient hf (Φ t x) hct).differentiableAt (by simp)
  have hB : DifferentiableAt ℝ B (q (t, d x)) :=
    ((g.contDiffOn_chartCoefficients (Φ t x)).contDiffAt
      (extChartAt_target_mem_nhds' hct)).differentiableAt (by simp)
  have hF (s : ℝ) : ContMDiff (𝓡 n) (𝓡 n) ∞ (Φ s) :=
    hs.comp (contMDiff_const.prodMk contMDiff_id)
  have hout : ∀ᶠ y in 𝓝 (d x), Φ t (d.symm y) ∈ c.source :=
    ((hF t _).comp (d x) hd).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (Φ t x)).mem_nhds
        (by simpa only [Function.comp_apply, hdx] using mem_extChartAt_source (I := 𝓡 n) (Φ t x)))
  have htime : ∀ᶠ y in 𝓝 (d x),
      HasDerivAt (fun s => q (s, y)) (G (q (t, y))) t := by
    filter_upwards [hout] with y hy
    have hh := hasDerivAt_chart_integralCurve (hΦ (d.symm y)) (Φ t x) t
      (by simpa only [c, extChartAt_source] using hy)
    have hgrad := mpullback_gradient_eq_chart_gradient (D := D) (f := f)
      (Φ t x) (c.map_source hy)
    change G (c (Φ t (d.symm y))) =
      mfderiv (𝓡 n) (𝓡 n) c (c.symm (c (Φ t (d.symm y))))
        (D.gradient f (c.symm (c (Φ t (d.symm y))))) at hgrad
    rw [c.left_inv hy] at hgrad
    change HasDerivAt (fun s => c (Φ s (d.symm y))) (G (c (Φ t (d.symm y)))) t
    rw [hgrad]
    exact hh
  have hpair := hasDerivAt_flow_metric_pairing_eq_zero hq hG hB htime
    (coordinate_gradient_metric_derivative_eq_zero hf hzero (Φ t x) hct) v w
  apply hpair.congr_of_eventuallyEq
  have ht : ContinuousAt (fun s => Φ s x) t :=
    (hs.comp (contMDiff_id.prodMk contMDiff_const)).continuous.continuousAt
  filter_upwards [ht.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓡 n) (Φ t x)).mem_nhds
      (mem_extChartAt_source _))] with s hsx
  simpa +instances only [q, B, c, d, Function.comp_def, extChartAt_to_inv] using
    (metric_pullback_in_charts (g := g) (hF s x) (Φ t x) hsx v w).symm



theorem gradientFlow_preserves_metric
    {D : LeviCivitaData g} {f : M → ℝ} {Φ : ℝ → M → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hzero : HasZeroHessian D f)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (fun z : ℝ × M => Φ z.1 z.2))
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient f))
    (h0 : ∀ x, Φ 0 x = x) (t : ℝ) (x : M) (v w : TangentSpace (𝓡 n) x) :
    g.inner (Φ t x) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v)
      (mfderiv (𝓡 n) (𝓡 n) (Φ t) x w) = g.inner x v w := by
  have hd := hasDerivAt_gradientFlow_metric_pairing_eq_zero hf hzero hs hΦ x v w
  have heq := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have hfun : Φ 0 = id := funext h0
  have hid : mfderiv (𝓡 n) (𝓡 n) (Φ 0) x = ContinuousLinearMap.id ℝ _ := by
    rw [hfun]
    exact mfderiv_id
  rw [hid, h0] at heq
  exact heq

end PoincareConjecture.RiemannianMetric
