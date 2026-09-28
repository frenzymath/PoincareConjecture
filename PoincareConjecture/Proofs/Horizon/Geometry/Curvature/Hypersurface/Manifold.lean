import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Charts

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open PoincareConjecture Filter
open scoped ContDiff Topology Manifold Bundle InnerProductSpace

namespace Poincare.Geometry.Curvature.Hypersurface

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

variable {m : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace (E (m + 1)) L] [IsManifold (𝓡 (m + 1)) ∞ L]
  [ChartedSpace (E (m + 2)) M] [IsManifold (𝓡 (m + 2)) ∞ M]

structure InducedChartRealization
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    (f : L → M) (x : L)
    (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b)) where
  gE : RiemannianMetric (m + 2) (E (m + 2))
  D : LeviCivitaData gE
  hE : RiemannianMetric (m + 1) (E (m + 1))
  D' : LeviCivitaData hE
  ambient_metric : ∀ᶠ y in 𝓝 (extChartAt (𝓡 (m + 2)) (f x) (f x)), ∀ a b,
    gE.inner y a b =
      g.inner ((extChartAt (𝓡 (m + 2)) (f x)).symm y)
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
          (extChartAt (𝓡 (m + 2)) (f x)).symm y a)
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
          (extChartAt (𝓡 (m + 2)) (f x)).symm y b)
  source_metric : ∀ᶠ y in 𝓝 (extChartAt (𝓡 (m + 1)) x x), ∀ a b,
    hE.inner y a b =
      h.inner ((extChartAt (𝓡 (m + 1)) x).symm y)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
          (extChartAt (𝓡 (m + 1)) x).symm y a)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
          (extChartAt (𝓡 (m + 1)) x).symm y b)
  immersion_metric : ∀ᶠ y in 𝓝 (extChartAt (𝓡 (m + 1)) x x), ∀ a b,
    hE.inner y a b =
      gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x y)
        (fderiv ℝ (immersionInCharts (m := m + 1) (n := m + 2) f x) y a)
        (fderiv ℝ (immersionInCharts (m := m + 1) (n := m + 2) f x) y b)

noncomputable def inducedChartRealization
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b)) :
    InducedChartRealization g h f x hf hmetric := by
  have hex := exists_induced_metric_in_charts g h hf x hmetric
  let gE := Classical.choose hex
  have hex₁ := Classical.choose_spec hex
  let D := Classical.choose hex₁
  have hex₂ := Classical.choose_spec hex₁
  let hE := Classical.choose hex₂
  have hex₃ := Classical.choose_spec hex₂
  let D' := Classical.choose hex₃
  have hex₄ := Classical.choose_spec hex₃
  exact ⟨gE, D, hE, D', hex₄.1, hex₄.2.1, hex₄.2.2⟩

noncomputable def chartShapeOperator
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x)) :
    TangentSpace (𝓡 (m + 1)) x →ₗ[ℝ] TangentSpace (𝓡 (m + 1)) x := by
  let R := inducedChartRealization g h hf x hmetric
  let c := extChartAt (𝓡 (m + 1)) x
  let d := extChartAt (𝓡 (m + 2)) (f x)
  let F := immersionInCharts (m := m + 1) (n := m + 2) f x
  exact (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c.symm (c x)).toLinearMap.comp
    ((shapeOperator R.D R.D' F (c x)
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d (f x) N)).comp
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c x).toLinearMap)

noncomputable def normalShapeOperator
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x)) :
    TangentSpace (𝓡 (m + 1)) x →ₗ[ℝ] TangentSpace (𝓡 (m + 1)) x :=
  chartShapeOperator g h hf x hmetric (-N)

private theorem source_chart_deriv_left_inverse
    (x : L) (w : TangentSpace (𝓡 (m + 1)) x) :
    mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
        (extChartAt (𝓡 (m + 1)) x).symm
        (extChartAt (𝓡 (m + 1)) x x)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
          (extChartAt (𝓡 (m + 1)) x) x w) = w := by
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓡 (m + 1)) (mem_extChartAt_source x)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
  exact congrArg (fun L => L w) hi

private theorem source_chart_deriv_right_inverse
    (x : L) (z : E (m + 1)) :
    mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
        (extChartAt (𝓡 (m + 1)) x) x
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
          (extChartAt (𝓡 (m + 1)) x).symm
          (extChartAt (𝓡 (m + 1)) x x) z) = z := by
  have hi := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := 𝓡 (m + 1)) (mem_extChartAt_target x)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
  have hp : (extChartAt (𝓡 (m + 1)) x).symm
      ((extChartAt (𝓡 (m + 1)) x) x) = x :=
    (extChartAt (𝓡 (m + 1)) x).left_inv (mem_extChartAt_source x)
  rw [hp] at hi
  exact congrArg (fun L => L z) hi

theorem ambient_chart_deriv_left_inverse
    (x : M) (w : TangentSpace (𝓡 (m + 2)) x) :
    mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
        (extChartAt (𝓡 (m + 2)) x).symm
        (extChartAt (𝓡 (m + 2)) x x)
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
          (extChartAt (𝓡 (m + 2)) x) x w) = w := by
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓡 (m + 2)) (mem_extChartAt_source x)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
  exact congrArg (fun L => L w) hi

theorem chart_normal_coordinate_unit
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x))
    (hN : g.inner (f x) N N = 1) :
    let R := inducedChartRealization g h hf x hmetric
    R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
      (extChartAt (𝓡 (m + 1)) x x))
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
        (extChartAt (𝓡 (m + 2)) (f x)) (f x) N)
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
        (extChartAt (𝓡 (m + 2)) (f x)) (f x) N) = 1 := by
  let R := inducedChartRealization g h hf x hmetric
  let c := extChartAt (𝓡 (m + 2)) (f x)
  let y := c (f x)
  have hp : c.symm y = f x := c.left_inv (mem_extChartAt_source (f x))
  have hFx : immersionInCharts (m := m + 1) (n := m + 2) f x
      (extChartAt (𝓡 (m + 1)) x x) = c (f x) := by
    unfold immersionInCharts
    rw [(extChartAt (𝓡 (m + 1)) x).left_inv (mem_extChartAt_source x)]
  dsimp only
  rw [hFx]
  rw [R.ambient_metric.self_of_nhds]
  rw [ambient_chart_deriv_left_inverse, hp]
  exact hN

theorem hasEigenvalue_conjugate_of_right_inverse
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℝ V] [Module ℝ W]
    (A : W →ₗ[ℝ] W) (P : V →ₗ[ℝ] W) (Q : W →ₗ[ℝ] V)
    (hPQ : P.comp Q = LinearMap.id) (κ : ℝ)
    (hκ : Module.End.HasEigenvalue A κ) :
    Module.End.HasEigenvalue (Q.comp (A.comp P)) κ := by
  obtain ⟨z, hz⟩ := hκ.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := Q z) ?_
  rw [Module.End.hasEigenvector_iff]
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    have hP : P (Q z) = z := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        congrArg (fun L => L z) hPQ
    simp only [LinearMap.comp_apply]
    rw [hP, hz.apply_eq_smul]
    simp only [map_smul]
  · intro hQz
    apply hz.2
    have hPQz := congrArg (fun L => L z) hPQ
    rw [LinearMap.comp_apply, hQz, map_zero] at hPQz
    exact hPQz.symm

theorem trace_conjugate_of_right_inverse
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℝ V] [Module ℝ W] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ W]
    (A : W →ₗ[ℝ] W) (P : V →ₗ[ℝ] W) (Q : W →ₗ[ℝ] V)
    (hPQ : P.comp Q = LinearMap.id) :
    LinearMap.trace ℝ V (Q.comp (A.comp P)) =
      LinearMap.trace ℝ W A := by
  rw [LinearMap.trace_comp_cycle A Q P]
  change LinearMap.trace ℝ W ((A.comp P).comp Q) = _
  rw [LinearMap.comp_assoc, hPQ, LinearMap.comp_id]

theorem chartShapeOperator_hasEigenvalue_of_coordinate
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x)) (κ : ℝ)
    (hκ : let R := inducedChartRealization g h hf x hmetric
      Module.End.HasEigenvalue
        (shapeOperator R.D R.D'
          (immersionInCharts (m := m + 1) (n := m + 2) f x)
          (extChartAt (𝓡 (m + 1)) x x)
          (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
            (extChartAt (𝓡 (m + 2)) (f x)) (f x) N)) κ) :
    Module.End.HasEigenvalue (chartShapeOperator g h hf x hmetric N) κ := by
  let R := inducedChartRealization g h hf x hmetric
  let c := extChartAt (𝓡 (m + 1)) x
  let d := extChartAt (𝓡 (m + 2)) (f x)
  let F := immersionInCharts (m := m + 1) (n := m + 2) f x
  let P := (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c x).toLinearMap
  let Q := (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c.symm (c x)).toLinearMap
  have hPQ : P.comp Q = LinearMap.id := by
    ext z
    exact source_chart_deriv_right_inverse x z
  apply hasEigenvalue_conjugate_of_right_inverse
    (shapeOperator R.D R.D' F (c x)
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d (f x) N)) P Q hPQ κ
  simpa only [R, c, d, F] using hκ

theorem coordinate_shapeOperator_hasEigenvalue_of_chartShapeOperator
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x)) (κ : ℝ)
    (hκ : Module.End.HasEigenvalue (chartShapeOperator g h hf x hmetric N) κ) :
    Module.End.HasEigenvalue
      (shapeOperator (inducedChartRealization g h hf x hmetric).D
        (inducedChartRealization g h hf x hmetric).D'
        (immersionInCharts (m := m + 1) (n := m + 2) f x)
        (extChartAt (𝓡 (m + 1)) x x)
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
          (extChartAt (𝓡 (m + 2)) (f x)) (f x) N)) κ := by
  let R := inducedChartRealization g h hf x hmetric
  let c := extChartAt (𝓡 (m + 1)) x
  let d := extChartAt (𝓡 (m + 2)) (f x)
  let F := immersionInCharts (m := m + 1) (n := m + 2) f x
  let P := (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c x).toLinearMap
  let Q := (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c.symm (c x)).toLinearMap
  have hQP : Q.comp P = LinearMap.id := by
    ext z
    exact source_chart_deriv_left_inverse x z
  have hPQ : P.comp Q = LinearMap.id := by
    ext z
    exact source_chart_deriv_right_inverse x z
  let A := shapeOperator R.D R.D' F (c x)
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d (f x) N)
  have hcoord := hasEigenvalue_conjugate_of_right_inverse
    (chartShapeOperator g h hf x hmetric N) Q P hQP κ hκ
  have hcoord' : Module.End.HasEigenvalue
      (P.comp ((Q.comp (A.comp P)).comp Q)) κ := by
    simpa only [chartShapeOperator, R, c, d, F, P, Q, A] using hcoord
  have hop : P.comp ((Q.comp (A.comp P)).comp Q) = A := by
    calc
      P.comp ((Q.comp (A.comp P)).comp Q) =
          (P.comp Q).comp (A.comp (P.comp Q)) := by rfl
      _ = A := by
        rw [hPQ, LinearMap.id_comp]
        exact LinearMap.comp_id A
  rw [hop] at hcoord'
  simpa only [A, R, c, d, F] using hcoord'

theorem chartShapeOperator_trace_eq_coordinate
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x)) :
    LinearMap.trace ℝ (TangentSpace (𝓡 (m + 1)) x)
        (chartShapeOperator g h hf x hmetric N) =
      let R := inducedChartRealization g h hf x hmetric
      LinearMap.trace ℝ (E (m + 1))
        (shapeOperator R.D R.D'
          (immersionInCharts (m := m + 1) (n := m + 2) f x)
          (extChartAt (𝓡 (m + 1)) x x)
          (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
            (extChartAt (𝓡 (m + 2)) (f x)) (f x) N)) := by
  let R := inducedChartRealization g h hf x hmetric
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 (m + 1)) x) :=
    inferInstanceAs (FiniteDimensional ℝ (E (m + 1)))
  let c := extChartAt (𝓡 (m + 1)) x
  let d := extChartAt (𝓡 (m + 2)) (f x)
  let F := immersionInCharts (m := m + 1) (n := m + 2) f x
  let P := (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c x).toLinearMap
  let Q := (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c.symm (c x)).toLinearMap
  have hPQ : P.comp Q = LinearMap.id := by
    ext z
    exact source_chart_deriv_right_inverse x z
  exact trace_conjugate_of_right_inverse
    (shapeOperator R.D R.D' F (c x)
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d (f x) N)) P Q hPQ

theorem sectionalCurvature_lower_bound_in_chart
    (g : RiemannianMetric (m + 2) M)
    (h : RiemannianMetric (m + 1) L) (D : LeviCivitaData h)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : E (m + 2)) (hN : let R := inducedChartRealization g h hf x hmetric
      R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) N N = 1)
    (hNT : let R := inducedChartRealization g h hf x hmetric
      ∀ a, R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) N
        (fderiv ℝ (immersionInCharts (m := m + 1) (n := m + 2) f x)
          (extChartAt (𝓡 (m + 1)) x x) a) = 0)
    (K β : ℝ) (hβ : 0 ≤ β)
    (hambient : let R := inducedChartRealization g h hf x hmetric
      ∀ a b, R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) a a = 1 →
      R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) b b = 1 →
      R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) a b = 0 →
      -K ≤ R.D.sectionalCurvature
        (immersionInCharts (m := m + 1) (n := m + 2) f x
          (extChartAt (𝓡 (m + 1)) x x)) a b)
    (hupper : let R := inducedChartRealization g h hf x hmetric
      ∀ κ, Module.End.HasEigenvalue
        (shapeOperator R.D R.D'
          (immersionInCharts (m := m + 1) (n := m + 2) f x)
          (extChartAt (𝓡 (m + 1)) x x) N) κ → κ ≤ β)
    (u v : E (m + 1))
    (hu : (let R := inducedChartRealization g h hf x hmetric
      R.hE.inner (extChartAt (𝓡 (m + 1)) x x) u u) = 1)
    (hv : (let R := inducedChartRealization g h hf x hmetric
      R.hE.inner (extChartAt (𝓡 (m + 1)) x x) v v) = 1)
    (huv : (let R := inducedChartRealization g h hf x hmetric
      R.hE.inner (extChartAt (𝓡 (m + 1)) x x) u v) = 0) :
    let R := inducedChartRealization g h hf x hmetric;
    -K - (negativePart ((shapeOperator R.D R.D'
      (immersionInCharts (m := m + 1) (n := m + 2) f x)
        (extChartAt (𝓡 (m + 1)) x x) N).trace ℝ (E (m + 1))) +
      ((m + 1 : ℕ) : ℝ) * β) * β ≤ D.sectionalCurvature
      ((extChartAt (𝓡 (m + 1)) x).symm
        ((extChartAt (𝓡 (m + 1)) x) x))
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
        (extChartAt (𝓡 (m + 1)) x).symm
        ((extChartAt (𝓡 (m + 1)) x) x) u)
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
        (extChartAt (𝓡 (m + 1)) x).symm
        ((extChartAt (𝓡 (m + 1)) x) x) v) := by
  let R := inducedChartRealization g h hf x hmetric
  let c := extChartAt (𝓡 (m + 1)) x
  let y := c x
  let F := immersionInCharts (m := m + 1) (n := m + 2) f x
  have hc : ContMDiffAt (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hinv : ∀ᶠ z in 𝓝 y,
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c.symm z).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target x)] with z hz
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hz
  have hcu : R.hE.inner y u u = 1 := by
    change R.hE.inner (extChartAt (𝓡 (m + 1)) x x) u u = 1
    exact hu
  have hcv : R.hE.inner y v v = 1 := by
    change R.hE.inner (extChartAt (𝓡 (m + 1)) x x) v v = 1
    exact hv
  have hcuv : R.hE.inner y u v = 0 := by
    change R.hE.inner (extChartAt (𝓡 (m + 1)) x x) u v = 0
    exact huv
  have hF := immersionInCharts_eventually_contDiffAt hf x
  have hcoord := sectionalCurvature_lower_bound_of_eventually R.D R.D' hF
    R.immersion_metric N hN hNT K β hβ hambient hupper u v hcu hcv hcuv
  have hpull := PoincareConjecture.LeviCivitaData.sectionalCurvature_eq_pullback_euclidean
    R.D' D hc hinv R.source_metric u v
  rw [hpull] at hcoord
  simpa [R, F, c, y] using hcoord

theorem sectionalCurvature_lower_bound_in_chartShapeOperator
    (g : RiemannianMetric (m + 2) M)
    (h : RiemannianMetric (m + 1) L) (D : LeviCivitaData h)
    {f : L → M} (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ f) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b =
        g.inner (f p) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) f p b))
    (N : TangentSpace (𝓡 (m + 2)) (f x)) (Ncoord : E (m + 2))
    (hNcoord : let R := inducedChartRealization g h hf x hmetric
      R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) Ncoord Ncoord = 1)
    (hNTcoord : let R := inducedChartRealization g h hf x hmetric
      ∀ a, R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) Ncoord
        (fderiv ℝ (immersionInCharts (m := m + 1) (n := m + 2) f x)
          (extChartAt (𝓡 (m + 1)) x x) a) = 0)
    (hNcoord_eq : Ncoord =
      mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
        (extChartAt (𝓡 (m + 2)) (f x)) (f x) N)
    (K β : ℝ) (hβ : 0 ≤ β)
    (hambient : let R := inducedChartRealization g h hf x hmetric
      ∀ a b, R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) a a = 1 →
      R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) b b = 1 →
      R.gE.inner (immersionInCharts (m := m + 1) (n := m + 2) f x
        (extChartAt (𝓡 (m + 1)) x x)) a b = 0 →
      -K ≤ R.D.sectionalCurvature
        (immersionInCharts (m := m + 1) (n := m + 2) f x
          (extChartAt (𝓡 (m + 1)) x x)) a b)
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
      D.sectionalCurvature
        ((extChartAt (𝓡 (m + 1)) x).symm
          ((extChartAt (𝓡 (m + 1)) x) x))
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
          (extChartAt (𝓡 (m + 1)) x).symm
          ((extChartAt (𝓡 (m + 1)) x) x) u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
          (extChartAt (𝓡 (m + 1)) x).symm
          ((extChartAt (𝓡 (m + 1)) x) x) v) := by
  let R := inducedChartRealization g h hf x hmetric
  have hupper_coord : ∀ κ, Module.End.HasEigenvalue
      (shapeOperator R.D R.D'
        (immersionInCharts (m := m + 1) (n := m + 2) f x)
        (extChartAt (𝓡 (m + 1)) x x) Ncoord) κ → κ ≤ β := by
    intro κ hκ
    apply hupper
    have hκ' := chartShapeOperator_hasEigenvalue_of_coordinate
      g h hf x hmetric N κ
    apply hκ'
    simpa [hNcoord_eq] using hκ
  have hbound := sectionalCurvature_lower_bound_in_chart g h D hf x hmetric
    Ncoord hNcoord hNTcoord K β hβ hambient hupper_coord u v hu hv huv
  have htrace := chartShapeOperator_trace_eq_coordinate g h hf x hmetric N
  rw [hNcoord_eq] at hbound
  dsimp only at hbound htrace
  rw [← htrace] at hbound
  simpa [R] using hbound

end Poincare.Geometry.Curvature.Hypersurface
