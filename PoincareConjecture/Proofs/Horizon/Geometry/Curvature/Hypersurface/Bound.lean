import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Manifold

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open PoincareConjecture Filter
open scoped ContDiff Topology Manifold Bundle

namespace Poincare.Geometry.Curvature.Hypersurface

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private theorem chart_symm_deriv {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M] (x : M) (v : E n) :
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
      (extChartAt (𝓡 n) x x) v = v := by
  have hi := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
  exact congrArg (fun A => A v) hi

private theorem metric_chart_at {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (gE : RiemannianMetric n (E n)) (x : M)
    (hm : ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x), ∀ a b,
      gE.inner y a b = g.inner ((extChartAt (𝓡 n) x).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y a)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y b))
    (u v : E n) : gE.inner (extChartAt (𝓡 n) x x) u v = g.inner x u v := by
  rw [hm.self_of_nhds, chart_symm_deriv, chart_symm_deriv]
  rw [(extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)]

private theorem sectional_chart_at {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {gE : RiemannianMetric n (E n)}
    (D : LeviCivitaData g) (DE : LeviCivitaData gE) (x : M)
    (hm : ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x), ∀ a b,
      gE.inner y a b = g.inner ((extChartAt (𝓡 n) x).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y a)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y b))
    (u v : E n) : DE.sectionalCurvature (extChartAt (𝓡 n) x x) u v =
      D.sectionalCurvature x u v := by
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) x).symm
      (extChartAt (𝓡 n) x x) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hi : ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x),
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target x)] with y hy
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  rw [DE.sectionalCurvature_eq_pullback_euclidean D hc hi hm,
    chart_symm_deriv, chart_symm_deriv]
  rw [(extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)]

theorem ambient_sectional_lower_bound_in_chart
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (gE : RiemannianMetric n (E n)) (DE : LeviCivitaData gE) (x : M)
    (hm : ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x), ∀ a b,
      gE.inner y a b = g.inner ((extChartAt (𝓡 n) x).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y a)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y b))
    (K : ℝ)
    (hambient : ∀ a b, g.inner x a a = 1 → g.inner x b b = 1 →
      g.inner x a b = 0 → -K ≤ D.sectionalCurvature x a b)
    (a b : E n) (ha : gE.inner (extChartAt (𝓡 n) x x) a a = 1)
    (hb : gE.inner (extChartAt (𝓡 n) x x) b b = 1)
    (hab : gE.inner (extChartAt (𝓡 n) x x) a b = 0) :
    -K ≤ DE.sectionalCurvature (extChartAt (𝓡 n) x x) a b := by
  have hmetric := metric_chart_at g gE x hm
  have ha' : g.inner x
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
        (extChartAt (𝓡 n) x x) a)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
        (extChartAt (𝓡 n) x x) a) = 1 := by
    simpa only [chart_symm_deriv] using (hmetric a a).symm.trans ha
  have hb' : g.inner x
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
        (extChartAt (𝓡 n) x x) b)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
        (extChartAt (𝓡 n) x x) b) = 1 := by
    simpa only [chart_symm_deriv] using (hmetric b b).symm.trans hb
  have hab' : g.inner x
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
        (extChartAt (𝓡 n) x x) a)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
        (extChartAt (𝓡 n) x x) b) = 0 := by
    simpa only [chart_symm_deriv] using (hmetric a b).symm.trans hab
  have hsec := hambient _ _ ha' hb' hab'
  rw [sectional_chart_at D DE x hm a b]
  simpa only [chart_symm_deriv] using hsec

theorem chart_normal_coordinate_orthogonal
    {m : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
    [ChartedSpace (E (m + 1)) L] [IsManifold (𝓡 (m + 1)) ∞ L]
    [ChartedSpace (E (m + 2)) M] [IsManifold (𝓡 (m + 2)) ∞ M]
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x))
    (hNT : ∀ w, g.inner (f x) N
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f x w) = 0) :
    let R := inducedChartRealization g h hf x hmetric;
    ∀ a, R.gE.inner
        (immersionInCharts (m := m + 1) (n := m + 2) f x
          (extChartAt (𝓡 (m + 1)) x x))
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
          (extChartAt (𝓡 (m + 2)) (f x)) (f x) N)
      (fderiv ℝ (immersionInCharts (m := m + 1) (n := m + 2) f x)
          (extChartAt (𝓡 (m + 1)) x x) a) = 0 := by
  dsimp only
  intro a
  let R := inducedChartRealization g h hf x hmetric
  let c := extChartAt (𝓡 (m + 1)) x
  let d := extChartAt (𝓡 (m + 2)) (f x)
  let F := immersionInCharts (m := m + 1) (n := m + 2) f x
  let y := c x
  have hp : c.symm y = x := c.left_inv (mem_extChartAt_source x)
  have hFy : F y = d (f x) := by
    change d (f (c.symm (c x))) = d (f x)
    rw [hp]
  have hc : ContMDiffAt (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hFnear := immersionInCharts_eventually_contDiffAt hf x
  have hFd : DifferentiableAt ℝ
      (immersionInCharts (m := m + 1) (n := m + 2) f x)
      (extChartAt (𝓡 (m + 1)) x x) :=
    hFnear.self_of_nhds.differentiableAt (by simp)
  have hF : MDifferentiableAt (𝓡 (m + 1)) (𝓡 (m + 2)) F y :=
    mdifferentiableAt_iff_differentiableAt.mpr
      (by simpa only [F, y, c] using hFd)
  have hfc : ∀ᶠ z in 𝓝 y, f (c.symm z) ∈ d.source := by
    apply (hf.continuous.continuousAt.comp hc.continuousAt).eventually
    simpa [hp, d] using (isOpen_extChartAt_source (I := 𝓡 (m + 2)) (f x)).mem_nhds
      (mem_extChartAt_source (f x))
  have hcomm : (d.symm ∘ F) =ᶠ[𝓝 y] (f ∘ c.symm) := by
    filter_upwards [hfc] with z hz
    exact d.left_inv hz
  have hd : MDifferentiableAt (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) := by
    have hyd : F y ∈ d.target := d.map_source (hfc.self_of_nhds)
    exact (contMDiffWithinAt_extChartAt_symm_target (n := ∞) (f x) hyd).contMDiffAt
      (extChartAt_target_mem_nhds' hyd) |>.mdifferentiableAt (by simp)
  have hc' : MDifferentiableAt (𝓡 (m + 1)) (𝓡 (m + 1)) c.symm y := hc.mdifferentiableAt (by simp)
  have he := hcomm.mfderiv_eq (I := 𝓡 (m + 1)) (I' := 𝓡 (m + 2))
  rw [mfderiv_comp y hd hF, mfderiv_comp y
    (hf.contMDiffAt.mdifferentiableAt (by simp)) hc'] at he
  have he' := congrArg (fun A => A a) he
  change mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y)
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F y a) =
    mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f (c.symm y)
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c.symm y a) at he'
  rw [mfderiv_eq_fderiv] at he'
  have he'' : mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (d (f x))
        (fderiv ℝ F y a) =
      mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f (c.symm y)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c.symm y a) := by
    rw [← hFy]
    exact he'
  have hmetricN := R.ambient_metric.self_of_nhds
  have hNinv : mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (d (f x))
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d (f x) N) = N := by
    simpa only [d] using ambient_chart_deriv_left_inverse (x := f x) N
  have hpD : d.symm (d (f x)) = f x :=
    d.left_inv (mem_extChartAt_source (f x))
  change R.gE.inner (F y)
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d (f x) N)
      (fderiv ℝ F y a) = 0
  rw [hFy, hmetricN]
  change g.inner (d.symm (d (f x)))
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (d (f x))
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d (f x) N))
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (d (f x))
        (fderiv ℝ F y a)) = 0
  rw [he'', hNinv, hpD, hp]
  exact hNT _

theorem sectionalCurvature_lower_bound_on_manifold
    {m : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
    [ChartedSpace (E (m + 1)) L] [IsManifold (𝓡 (m + 1)) ∞ L]
    [ChartedSpace (E (m + 2)) M] [IsManifold (𝓡 (m + 2)) ∞ M]
    (g : RiemannianMetric (m + 2) M)
    (h : RiemannianMetric (m + 1) L)
    (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x))
    (hN : g.inner (f x) N N = 1)
    (hNT : ∀ w, g.inner (f x) N
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f x w) = 0)
    (K β : ℝ) (hβ : 0 ≤ β)
    (hambient : ∀ a b, g.inner (f x) a a = 1 → g.inner (f x) b b = 1 →
      g.inner (f x) a b = 0 → -K ≤ Dg.sectionalCurvature (f x) a b)
    (hupper : ∀ κ, Module.End.HasEigenvalue
      (chartShapeOperator g h hf x hmetric N) κ → κ ≤ β)
    (u v : E (m + 1))
    (hu : (let R := inducedChartRealization g h hf x hmetric
      R.hE.inner (extChartAt (𝓡 (m + 1)) x x) u u) = 1)
    (hv : (let R := inducedChartRealization g h hf x hmetric
      R.hE.inner (extChartAt (𝓡 (m + 1)) x x) v v) = 1)
    (huv : (let R := inducedChartRealization g h hf x hmetric
      R.hE.inner (extChartAt (𝓡 (m + 1)) x x) u v) = 0) :
    let R := inducedChartRealization g h hf x hmetric;
    -K - (negativePart ((chartShapeOperator g h hf x hmetric N).trace ℝ
      (TangentSpace (𝓡 (m + 1)) x)) + ((m + 1 : ℕ) : ℝ) * β) * β ≤
      Dh.sectionalCurvature
        ((extChartAt (𝓡 (m + 1)) x).symm
          ((extChartAt (𝓡 (m + 1)) x) x))
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
          (extChartAt (𝓡 (m + 1)) x).symm
          ((extChartAt (𝓡 (m + 1)) x) x) u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
          (extChartAt (𝓡 (m + 1)) x).symm
          ((extChartAt (𝓡 (m + 1)) x) x) v) := by
  let R := inducedChartRealization g h hf x hmetric
  let Ncoord := mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
    (extChartAt (𝓡 (m + 2)) (f x)) (f x) N
  have hFy : immersionInCharts (m := m + 1) (n := m + 2) f x
      (extChartAt (𝓡 (m + 1)) x x) =
      extChartAt (𝓡 (m + 2)) (f x) (f x) := by
    unfold immersionInCharts
    rw [(extChartAt (𝓡 (m + 1)) x).left_inv (mem_extChartAt_source x)]
  have hNcoord := chart_normal_coordinate_unit g h hf x hmetric N hN
  have hNTcoord := chart_normal_coordinate_orthogonal g h hf x hmetric N hNT
  have hambient_coord : let R := inducedChartRealization g h hf x hmetric
      ∀ a b, R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) a a = 1 →
      R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) b b = 1 →
      R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) a b = 0 →
      -K ≤ R.D.sectionalCurvature
        (immersionInCharts (m := m + 1) (n := m + 2) f x
          (extChartAt (𝓡 (m + 1)) x x)) a b := by
    dsimp only
    intro a b ha hb hab
    have ha' : R.gE.inner (extChartAt (𝓡 (m + 2)) (f x) (f x)) a a = 1 := by
      rw [← hFy]
      exact ha
    have hb' : R.gE.inner (extChartAt (𝓡 (m + 2)) (f x) (f x)) b b = 1 := by
      rw [← hFy]
      exact hb
    have hab' : R.gE.inner (extChartAt (𝓡 (m + 2)) (f x) (f x)) a b = 0 := by
      rw [← hFy]
      exact hab
    rw [hFy]
    exact ambient_sectional_lower_bound_in_chart g Dg R.gE R.D (f x)
      R.ambient_metric K hambient a b ha' hb' hab'
  have hbound := sectionalCurvature_lower_bound_in_chartShapeOperator
    g h Dh hf x hmetric N Ncoord hNcoord hNTcoord rfl K β hβ
      hambient_coord hupper u v hu hv huv
  simpa [R, Ncoord] using hbound

theorem chartShapeOperator_selfAdjoint
    {m : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
    [ChartedSpace (E (m + 1)) L] [IsManifold (𝓡 (m + 1)) ∞ L]
    [ChartedSpace (E (m + 2)) M] [IsManifold (𝓡 (m + 2)) ∞ M]
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x))
    (u v : TangentSpace (𝓡 (m + 1)) x) :
    h.inner x (chartShapeOperator g h hf x hmetric N u) v =
      h.inner x u (chartShapeOperator g h hf x hmetric N v) := by
  let R := inducedChartRealization g h hf x hmetric
  have hcoord := shapeOperator_selfAdjoint R.D R.D'
    (immersionInCharts_eventually_contDiffAt hf x).self_of_nhds
    (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
      (extChartAt (𝓡 (m + 2)) (f x)) (f x) N) u v
  rw [metric_chart_at h R.hE x R.source_metric,
    metric_chart_at h R.hE x R.source_metric] at hcoord
  have hshape (w : E (m + 1)) : chartShapeOperator g h hf x hmetric N w =
      shapeOperator R.D R.D'
        (immersionInCharts (m := m + 1) (n := m + 2) f x)
        (extChartAt (𝓡 (m + 1)) x x)
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
          (extChartAt (𝓡 (m + 2)) (f x)) (f x) N) w := by
    change mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
        (extChartAt (𝓡 (m + 1)) x).symm (extChartAt (𝓡 (m + 1)) x x)
        (shapeOperator R.D R.D' (immersionInCharts f x)
          (extChartAt (𝓡 (m + 1)) x x)
          (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
            (extChartAt (𝓡 (m + 2)) (f x)) (f x) N)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) (extChartAt (𝓡 (m + 1)) x) x w)) = _
    rw [chart_symm_deriv]
    have hw := congrArg (fun A => A w) (mfderiv_extChartAt_self (I := 𝓡 (m + 1)) (x := x))
    rw [hw]
    rfl
  rw [hshape u, hshape v]
  exact hcoord

theorem exists_chartShapeOperator_eigenbasis
    {m : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
    [ChartedSpace (E (m + 1)) L] [IsManifold (𝓡 (m + 1)) ∞ L]
    [ChartedSpace (E (m + 2)) M] [IsManifold (𝓡 (m + 2)) ∞ M]
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x)) :
    ∃ (κ : Fin (m + 1) → ℝ) (b : Module.Basis (Fin (m + 1)) ℝ (TangentSpace (𝓡 (m + 1)) x)),
      (∀ i j, h.inner x (b i) (b j) = if i = j then 1 else 0) ∧
      (∀ i, chartShapeOperator g h hf x hmetric N (b i) = κ i • b i) ∧
      (∀ i, Module.End.HasEigenvalue (chartShapeOperator g h hf x hmetric N) (κ i)) ∧
      (chartShapeOperator g h hf x hmetric N).trace ℝ
        (TangentSpace (𝓡 (m + 1)) x) = ∑ i, κ i := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : L → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 (m + 1)) x) := inferInstance
  let : InnerProductSpace ℝ (TangentSpace (𝓡 (m + 1)) x) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + 1)) x) :=
    inferInstanceAs (FiniteDimensional ℝ (E (m + 1)))
  let A := chartShapeOperator g h hf x hmetric N
  have hA : A.IsSymmetric := chartShapeOperator_selfAdjoint g h hf x hmetric N
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 (m + 1)) x) = m + 1 := by
    change Module.finrank ℝ (E (m + 1)) = m + 1
    simp [E]
  refine ⟨hA.eigenvalues hdim, (hA.eigenvectorBasis hdim).toBasis, ?_, ?_, ?_, ?_⟩
  · exact fun i j => (hA.eigenvectorBasis hdim).inner_eq_ite i j
  · exact hA.apply_eigenvectorBasis hdim
  · exact hA.hasEigenvalue_eigenvalues hdim
  · exact hA.trace_eq_sum_eigenvalues hdim

theorem sectionalCurvature_lower_bound_of_induced_metric
    {m : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) L]
    [IsManifold (𝓡 (m + 1)) ∞ L]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [IsManifold (𝓡 (m + 2)) ∞ M]
    (g : RiemannianMetric (m + 2) M)
    (h : RiemannianMetric (m + 1) L)
    (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x))
    (hN : g.inner (f x) N N = 1)
    (hNT : ∀ w, g.inner (f x) N
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f x w) = 0)
    (K β : ℝ) (hβ : 0 ≤ β)
    (hambient : ∀ a b, g.inner (f x) a a = 1 → g.inner (f x) b b = 1 →
      g.inner (f x) a b = 0 → -K ≤ Dg.sectionalCurvature (f x) a b)
    (hupper : ∀ κ, Module.End.HasEigenvalue
      (chartShapeOperator g h hf x hmetric N) κ → κ ≤ β)
    (u v : TangentSpace (𝓡 (m + 1)) x)
    (hu : h.inner x u u = 1) (hv : h.inner x v v = 1)
    (huv : h.inner x u v = 0) :
    -K - (negativePart ((chartShapeOperator g h hf x hmetric N).trace ℝ
      (TangentSpace (𝓡 (m + 1)) x)) + ((m + 1 : ℕ) : ℝ) * β) * β ≤
      Dh.sectionalCurvature x u v := by
  let R := inducedChartRealization g h hf x hmetric
  have hcu : R.hE.inner (extChartAt (𝓡 (m + 1)) x x) u u = 1 :=
    (metric_chart_at h R.hE x R.source_metric u u).trans hu
  have hcv : R.hE.inner (extChartAt (𝓡 (m + 1)) x x) v v = 1 :=
    (metric_chart_at h R.hE x R.source_metric v v).trans hv
  have hcuv : R.hE.inner (extChartAt (𝓡 (m + 1)) x x) u v = 0 :=
    (metric_chart_at h R.hE x R.source_metric u v).trans huv
  have hb := sectionalCurvature_lower_bound_on_manifold g h Dg Dh hf x hmetric
    N hN hNT K β hβ hambient hupper u v hcu hcv hcuv
  rw [chart_symm_deriv, chart_symm_deriv,
    (extChartAt (𝓡 (m + 1)) x).left_inv (mem_extChartAt_source x)] at hb
  exact hb

theorem sectionalCurvature_lower_bound_of_normal_curvatures
    {m : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) L]
    [IsManifold (𝓡 (m + 1)) ∞ L]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [IsManifold (𝓡 (m + 2)) ∞ M]
    (g : RiemannianMetric (m + 2) M)
    (h : RiemannianMetric (m + 1) L)
    (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x))
    (hN : g.inner (f x) N N = 1)
    (hNT : ∀ w, g.inner (f x) N
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f x w) = 0)
    (K β : ℝ) (hβ : 0 ≤ β)
    (hambient : ∀ a b, g.inner (f x) a a = 1 → g.inner (f x) b b = 1 →
      g.inner (f x) a b = 0 → -K ≤ Dg.sectionalCurvature (f x) a b)
    (hupper : ∀ κ, Module.End.HasEigenvalue
      (normalShapeOperator g h hf x hmetric N) κ → κ ≤ β)
    (u v : TangentSpace (𝓡 (m + 1)) x)
    (hu : h.inner x u u = 1) (hv : h.inner x v v = 1)
    (huv : h.inner x u v = 0) :
    -K - (negativePart ((normalShapeOperator g h hf x hmetric N).trace ℝ
      (TangentSpace (𝓡 (m + 1)) x)) + ((m + 1 : ℕ) : ℝ) * β) * β ≤
      Dh.sectionalCurvature x u v := by
  have hnegN : g.inner (f x) (-N) (-N) = 1 := by
    simpa only [map_neg, neg_apply, neg_neg] using hN
  have hnegNT : ∀ w, g.inner (f x) (-N)
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f x w) = 0 := by
    intro w
    simp only [map_neg, neg_apply, hNT w, neg_zero]
  exact sectionalCurvature_lower_bound_of_induced_metric g h Dg Dh hf x hmetric
    (-N) hnegN hnegNT K β hβ hambient hupper u v hu hv huv

theorem no_unit_tangent_zero_dimensional
    {L : Type*} [TopologicalSpace L] [ChartedSpace (EuclideanSpace ℝ (Fin 0)) L]
    [IsManifold (𝓡 0) ∞ L] (h : RiemannianMetric 0 L) (x : L)
    (u : TangentSpace (𝓡 0) x) : h.inner x u u ≠ 1 := by
  have hu : u = 0 := by
    exact @Subsingleton.elim (EuclideanSpace ℝ (Fin 0)) inferInstance u 0
  simp [hu]

end Poincare.Geometry.Curvature.Hypersurface
