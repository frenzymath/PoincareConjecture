import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.ManifoldCurvatureSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem sectionalCurvature_eq_pullback_euclidean
    (D : LeviCivitaData gE) (D' : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin n),
      gE.inner y u v = g.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    (u v : EuclideanSpace ℝ (Fin n)) :
    D.sectionalCurvature x u v = D'.sectionalCurvature (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v) := by
  unfold sectionalCurvature
  rw [D.curvatureTensor_eq_pullback_euclidean D' hf hinv hmetric]
  rw [hmetric.self_of_nhds, hmetric.self_of_nhds, hmetric.self_of_nhds]

end PoincareConjecture.LeviCivitaData

namespace Poincare.Geometry.Curvature.Hypersurface

open PoincareConjecture

variable {m n : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) L] [IsManifold (𝓡 m) ∞ L]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def immersionInCharts (f : L → M) (x : L) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) :=
  fun y => extChartAt (𝓡 n) (f x) (f ((extChartAt (𝓡 m) x).symm y))

theorem immersionInCharts_eventually_contDiffAt
    {f : L → M} (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (x : L) :
    ∀ᶠ y in 𝓝 (extChartAt (𝓡 m) x x),
      ContDiffAt ℝ ∞ (immersionInCharts (m := m) (n := n) f x) y := by
  let c := extChartAt (𝓡 m) x
  let d := extChartAt (𝓡 n) (f x)
  have hc : ContMDiffAt (𝓡 m) (𝓡 m) ∞ c.symm (c x) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hp : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have ht : ∀ᶠ y in 𝓝 (c x), f (c.symm y) ∈ d.source := by
    have hcont := hf.continuous.continuousAt.comp hc.continuousAt
    apply hcont.eventually
    simpa [hp, d] using (isOpen_extChartAt_source (I := 𝓡 n) (f x)).mem_nhds
      (mem_extChartAt_source (f x))
  filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target x), ht]
    with y hy hfy
  have hcy : ContMDiffAt (𝓡 m) (𝓡 m) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hdy : ContMDiffAt (𝓡 n) (𝓡 n) ∞ d (f (c.symm y)) :=
    contMDiffAt_extChartAt' (by simpa only [d, extChartAt_source] using hfy)
  exact contMDiffAt_iff_contDiffAt.mp (hdy.comp y (hf.contMDiffAt.comp y hcy))

theorem induced_metric_in_commuting_charts
    (g : RiemannianMetric n M) (h : RiemannianMetric m L)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (hE : RiemannianMetric m (EuclideanSpace ℝ (Fin m)))
    {f : L → M} {c : EuclideanSpace ℝ (Fin m) → L}
    {d : EuclideanSpace ℝ (Fin n) → M}
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {y : EuclideanSpace ℝ (Fin m)}
    (hf : MDifferentiableAt (𝓡 m) (𝓡 n) f (c y))
    (hc : MDifferentiableAt (𝓡 m) (𝓡 m) c y)
    (hd : MDifferentiableAt (𝓡 n) (𝓡 n) d (F y))
    (hF : DifferentiableAt ℝ F y)
    (hcomm : (d ∘ F) =ᶠ[𝓝 y] (f ∘ c))
    (hfmetric : ∀ a b, h.inner (c y) a b =
      g.inner (f (c y)) (mfderiv (𝓡 m) (𝓡 n) f (c y) a)
        (mfderiv (𝓡 m) (𝓡 n) f (c y) b))
    (hcmetric : ∀ a b, hE.inner y a b =
      h.inner (c y) (mfderiv (𝓡 m) (𝓡 m) c y a)
        (mfderiv (𝓡 m) (𝓡 m) c y b))
    (hdmetric : ∀ a b, gE.inner (F y) a b =
      g.inner (d (F y)) (mfderiv (𝓡 n) (𝓡 n) d (F y) a)
        (mfderiv (𝓡 n) (𝓡 n) d (F y) b))
    (u v : EuclideanSpace ℝ (Fin m)) :
    hE.inner y u v = gE.inner (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) := by
  have hFe : MDifferentiableAt (𝓡 m) (𝓡 n) F y :=
    mdifferentiableAt_iff_differentiableAt.mpr hF
  have he := hcomm.mfderiv_eq (I := 𝓡 m) (I' := 𝓡 n)
  rw [mfderiv_comp y hd hFe, mfderiv_comp y hf hc] at he
  have hpoint : d (F y) = f (c y) := hcomm.self_of_nhds
  rw [hcmetric, hfmetric, hdmetric, hpoint]
  have he' (a : EuclideanSpace ℝ (Fin m)) :
      mfderiv (𝓡 n) (𝓡 n) d (F y) (fderiv ℝ F y a) =
        mfderiv (𝓡 m) (𝓡 n) f (c y) (mfderiv (𝓡 m) (𝓡 m) c y a) := by
    have hea := congrArg (fun A => A a) he
    change mfderiv (𝓡 n) (𝓡 n) d (F y) (mfderiv (𝓡 m) (𝓡 n) F y a) =
      mfderiv (𝓡 m) (𝓡 n) f (c y) (mfderiv (𝓡 m) (𝓡 m) c y a) at hea
    rw [mfderiv_eq_fderiv] at hea
    exact hea
  exact congrArg₂ (fun a b : EuclideanSpace ℝ (Fin n) => g.inner (f (c y)) a b)
    (he' u).symm (he' v).symm

theorem exists_induced_metric_in_charts
    (g : RiemannianMetric n M) (h : RiemannianMetric m L)
    {f : L → M} (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b, h.inner p a b =
      g.inner (f p) (mfderiv (𝓡 m) (𝓡 n) f p a)
        (mfderiv (𝓡 m) (𝓡 n) f p b)) :
    ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (_D : LeviCivitaData gE)
      (hE : RiemannianMetric m (EuclideanSpace ℝ (Fin m))) (_D' : LeviCivitaData hE),
      (∀ᶠ y in 𝓝 (extChartAt (𝓡 n) (f x) (f x)), ∀ a b,
        gE.inner y a b = g.inner ((extChartAt (𝓡 n) (f x)).symm y)
          (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (f x)).symm y a)
          (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (f x)).symm y b)) ∧
      (∀ᶠ y in 𝓝 (extChartAt (𝓡 m) x x), ∀ a b,
        hE.inner y a b = h.inner ((extChartAt (𝓡 m) x).symm y)
          (mfderiv (𝓡 m) (𝓡 m) (extChartAt (𝓡 m) x).symm y a)
          (mfderiv (𝓡 m) (𝓡 m) (extChartAt (𝓡 m) x).symm y b)) ∧
      (∀ᶠ y in 𝓝 (extChartAt (𝓡 m) x x), ∀ a b,
        hE.inner y a b = gE.inner (immersionInCharts (m := m) (n := n) f x y)
          (fderiv ℝ (immersionInCharts (m := m) (n := n) f x) y a)
          (fderiv ℝ (immersionInCharts (m := m) (n := n) f x) y b)) := by
  obtain ⟨gE, D, hgE⟩ := LeviCivitaData.exists_chart_metric g (f x)
  obtain ⟨hE, D', hhE⟩ := LeviCivitaData.exists_chart_metric h x
  refine ⟨gE, D, hE, D', hgE, hhE, ?_⟩
  let c := extChartAt (𝓡 m) x
  let d := extChartAt (𝓡 n) (f x)
  let F := immersionInCharts (m := m) (n := n) f x
  have hp : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hFp : F (c x) = d (f x) := by
    change d (f (c.symm (c x))) = d (f x)
    rw [hp]
  have hc : ContMDiffAt (𝓡 m) (𝓡 m) ∞ c.symm (c x) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hFnear := immersionInCharts_eventually_contDiffAt hf x
  have hFcont : ContinuousAt F (c x) := hFnear.self_of_nhds.continuousAt
  have hfc : ∀ᶠ y in 𝓝 (c x), f (c.symm y) ∈ d.source := by
    apply (hf.continuous.continuousAt.comp hc.continuousAt).eventually
    simpa [hp, d] using (isOpen_extChartAt_source (I := 𝓡 n) (f x)).mem_nhds
      (mem_extChartAt_source (f x))
  have hcomm : (d.symm ∘ F) =ᶠ[𝓝 (c x)] (f ∘ c.symm) := by
    filter_upwards [hfc] with y hy
    exact d.left_inv hy
  have hgEnear : ∀ᶠ y in 𝓝 (c x), ∀ a b : EuclideanSpace ℝ (Fin n), gE.inner (F y) a b =
      g.inner (d.symm (F y)) (mfderiv (𝓡 n) (𝓡 n) d.symm (F y) a)
        (mfderiv (𝓡 n) (𝓡 n) d.symm (F y) b) := by
    have hgE' : ∀ᶠ z in 𝓝 (F (c x)), ∀ a b : EuclideanSpace ℝ (Fin n),
        gE.inner z a b = g.inner (d.symm z) (mfderiv (𝓡 n) (𝓡 n) d.symm z a)
          (mfderiv (𝓡 n) (𝓡 n) d.symm z b) := by
      simpa only [hFp] using hgE
    exact hFcont.eventually hgE'
  have hmetricnear : ∀ᶠ y in 𝓝 (c x), ∀ a b, h.inner (c.symm y) a b =
      g.inner (f (c.symm y)) (mfderiv (𝓡 m) (𝓡 n) f (c.symm y) a)
        (mfderiv (𝓡 m) (𝓡 n) f (c.symm y) b) := by
    have hm' : ∀ᶠ p in 𝓝 (c.symm (c x)), ∀ a b, h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 m) (𝓡 n) f p a)
          (mfderiv (𝓡 m) (𝓡 n) f p b) := by
      simpa only [hp] using hmetric
    exact hc.continuousAt.eventually hm'
  filter_upwards [hhE, hgEnear, hmetricnear, hFnear, hfc,
    extChartAt_target_mem_nhds' (mem_extChartAt_target x), hcomm.eventually_nhds]
    with y hyh hyg hym hyF hyf hyc hycomm a b
  have hcy : ContMDiffAt (𝓡 m) (𝓡 m) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hyc).contMDiffAt
      (extChartAt_target_mem_nhds' hyc)
  have hyd : F y ∈ d.target := d.map_source hyf
  have hdy : ContMDiffAt (𝓡 n) (𝓡 n) ∞ d.symm (F y) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) (f x) hyd).contMDiffAt
      (extChartAt_target_mem_nhds' hyd)
  exact induced_metric_in_commuting_charts g h gE hE
    (hf.contMDiffAt.mdifferentiableAt (by simp)) (hcy.mdifferentiableAt (by simp))
    (hdy.mdifferentiableAt (by simp)) (hyF.differentiableAt (by simp))
    hycomm hym hyh hyg a b

end Poincare.Geometry.Curvature.Hypersurface
