import PoincareConjecture.Proofs.M60.Mathlib.SUCompactMetricCoefficients
import PoincareConjecture.Proofs.M60.Mathlib.MetricPullbackForm
import PoincareConjecture.Proofs.M60.Mathlib.PullbackMetricRegularity
import PoincareConjecture.Proofs.M60.Mathlib.CoordinateDerivative
import PoincareConjecture.Definitions.M60Area

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

def m60SUChartMetric (g : RiemannianMetric n M) (e : OpenPartialHomeomorph M E)
    (y : E) : E →L[ℝ] E →L[ℝ] ℝ := M60.metricPullbackForm g e.symm y

theorem m60SUChartMetric_apply (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph M E) (y v w : E) :
    m60SUChartMetric g e y v w = g.inner (e.symm y)
      (mfderiv (𝓡 n) (𝓡 n) e.symm y v) (mfderiv (𝓡 n) (𝓡 n) e.symm y w) := rfl

theorem m60SUChartMetric_continuousOn (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph M E)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target) :
    ContinuousOn (m60SUChartMetric g e) e.target := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hcolumn (v : E) : ContinuousOn (fun y : E =>
      (⟨e.symm y, mfderiv (𝓡 n) (𝓡 n) e.symm y v⟩ : TangentBundle (𝓡 n) M))
      e.target := by
    have ht := hei.continuousOn_tangentMapWithin le_rfl e.open_target.uniqueMDiffOn
    have hp := ht.comp
      ((tangentBundleModelSpaceHomeomorph (𝓡 n)).symm.continuous.comp
        (continuous_id.prodMk (continuous_const (y := v)))).continuousOn (fun _ hy => hy)
    apply hp.congr
    intro y hy
    change (⟨e.symm y, mfderiv (𝓡 n) (𝓡 n) e.symm y v⟩ : TangentBundle (𝓡 n) M) =
      ⟨e.symm y, mfderivWithin (𝓡 n) (𝓡 n) e.symm e.target y v⟩
    erw [mfderivWithin_of_mem_nhds (e.open_target.mem_nhds hy)]
  apply continuousOn_clm_apply.mpr
  intro v
  apply continuousOn_clm_apply.mpr
  intro w
  change ContinuousOn (fun y => g.inner (e.symm y)
    (mfderiv (𝓡 n) (𝓡 n) e.symm y v) (mfderiv (𝓡 n) (𝓡 n) e.symm y w)) e.target
  exact (hcolumn v).inner_bundle (hcolumn w)

theorem m60SUChartMetric_pos (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph M E) (he : e.MDifferentiable (𝓡 n) (𝓡 n))
    {y : E} (hy : y ∈ e.target) {v : E} (hv : v ≠ 0) :
    0 < m60SUChartMetric g e y v v := by
  apply g.pos
  intro hd
  have hid := congrArg (fun L => L v) (he.comp_symm_deriv hy)
  change mfderiv (𝓡 n) (𝓡 n) e (e.symm y)
    (mfderiv (𝓡 n) (𝓡 n) e.symm y v) = v at hid
  have : v = 0 := by
    erw [hd, map_zero] at hid
    exact hid.symm
  exact hv this

theorem m60SUChartMetric_compact_coercive (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph M E) (he : e.MDifferentiable (𝓡 n) (𝓡 n))
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKe : K ⊆ e.target) :
    ∃ a > 0, ∀ y ∈ K, ∀ v, a * ‖v‖ ^ 2 ≤ m60SUChartMetric g e y v v :=
  M60.suCompactMetric_coercive hK _ ((m60SUChartMetric_continuousOn g e hei).mono hKe)
    (fun _ hy _ hv => m60SUChartMetric_pos g e he (hKe hy) hv)

theorem m60AreaGram_eq_SUChartMetric (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph M E) (he : e.MDifferentiable (𝓡 n) (𝓡 n))
    {f : LoopPlane → M} {z : LoopPlane} (hf : ContinuousAt f z) (hz : f z ∈ e.source)
    (i j : Fin 2) :
    m60AreaGram g f z i j = m60SUChartMetric g e (e (f z))
      (fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ j)) := by
  have hd := M60.mfderiv_eq_inverse_chart_comp_fderiv e he hf hz
  have heq := e.left_inv hz
  have hi (v w : E) : g.inner (e.symm (e (f z))) v w = g.inner (f z) v w :=
    congrArg (fun p : M => g.inner p v w) heq
  simp only [m60AreaGram, m60SUChartMetric_apply, hd, hi]
  rfl

end PoincareConjecture
