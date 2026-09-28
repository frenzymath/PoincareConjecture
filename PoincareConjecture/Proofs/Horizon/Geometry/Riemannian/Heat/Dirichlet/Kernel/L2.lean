import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SpectralKernel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Semigroup
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Spectral.DirichletCounting












set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace NNReal Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

variable (D : LeviCivitaData g) (Ω : Set M) (hn : 0 < n)
  (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))


def heatKernelL2 (t : ℝ≥0) :
    Lp ℝ 2 ((g.volumeMeasure.restrict Ω).prod (g.volumeMeasure.restrict Ω)) :=
  Poincare.Analysis.Dirichlet.Spectral.kernelL2 (eigenbasis D Ω hn hΩ hc)
    (eigenvalueNN D Ω hn hΩ hc) t

include hc in
theorem domainMeasure_isFinite : IsFiniteMeasure (g.volumeMeasure.restrict Ω) :=
  isFiniteMeasure_restrict.mpr
    ((measure_mono (subset_closure : Ω ⊆ closure Ω)).trans_lt
      (g.volumeMeasure_lt_top_of_isCompact hc)).ne

include hn hΩ hc in
theorem summable_heatCoefficient (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : EigenIndex D Ω => Real.exp (-eigenvalue D Ω i * (t : ℝ))) := by
  simpa only [pow_zero, one_mul, neg_mul, mul_comm (t : ℝ)] using
    summable_eigenvalue_weighted_exp D Ω hn hΩ hc (t : ℝ) ht 0

theorem heatKernelL2_hasSum (t : ℝ≥0) (ht : 0 < t) :
    HasSum (fun i : EigenIndex D Ω =>
      Real.exp (-eigenvalue D Ω i * (t : ℝ)) •
        Poincare.Analysis.Dirichlet.tensorL2
          (eigenbasis D Ω hn hΩ hc i) (eigenbasis D Ω hn hΩ hc i))
      (heatKernelL2 D Ω hn hΩ hc t) := by
  let := domainMeasure_isFinite (g := g) Ω hc
  exact Poincare.Analysis.Dirichlet.Spectral.kernelL2_hasSum
    (eigenbasis D Ω hn hΩ hc) (eigenvalueNN D Ω hn hΩ hc) t
    (summable_heatCoefficient D Ω hn hΩ hc t ht)

theorem summable_norm_heatKernelL2 (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : EigenIndex D Ω =>
      ‖Real.exp (-eigenvalue D Ω i * (t : ℝ)) •
        Poincare.Analysis.Dirichlet.tensorL2
          (eigenbasis D Ω hn hΩ hc i) (eigenbasis D Ω hn hΩ hc i)‖) := by
  let := domainMeasure_isFinite (g := g) Ω hc
  exact Poincare.Analysis.Dirichlet.Spectral.summable_norm_kernelL2
    (eigenbasis D Ω hn hΩ hc) (eigenvalueNN D Ω hn hΩ hc) t
    (summable_heatCoefficient D Ω hn hΩ hc t ht)

theorem integrable_heatKernelL2_pair (t : ℝ≥0)
    (f h : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    Integrable (fun z : M × M => heatKernelL2 D Ω hn hΩ hc t z * h z.1 * f z.2)
      ((g.volumeMeasure.restrict Ω).prod (g.volumeMeasure.restrict Ω)) :=
  Poincare.Analysis.Dirichlet.Spectral.integrable_kernelL2_pair
    (eigenbasis D Ω hn hΩ hc) (eigenvalueNN D Ω hn hΩ hc) t f h

theorem integral_heatKernelL2_pair (t : ℝ≥0) (ht : 0 < t)
    (f h : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    (∫ z : M × M, heatKernelL2 D Ω hn hΩ hc t z * h z.1 * f z.2
      ∂((g.volumeMeasure.restrict Ω).prod (g.volumeMeasure.restrict Ω))) =
        ⟪heatSemigroup D Ω hn hΩ hc t f, h⟫_ℝ := by
  let := domainMeasure_isFinite (g := g) Ω hc
  exact Poincare.Analysis.Dirichlet.Spectral.integral_kernelL2_pair
    (eigenbasis D Ω hn hΩ hc) (eigenvalueNN D Ω hn hΩ hc) t
    (summable_heatCoefficient D Ω hn hΩ hc t ht) f h

theorem heatKernelL2_integral_ae (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    (heatSemigroup D Ω hn hΩ hc t f : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
      fun x => ∫ y, heatKernelL2 D Ω hn hΩ hc t (x, y) * f y
        ∂(g.volumeMeasure.restrict Ω) := by
  let := domainMeasure_isFinite (g := g) Ω hc
  exact Poincare.Analysis.Dirichlet.Spectral.kernelL2_integral_ae
    (eigenbasis D Ω hn hΩ hc) (eigenvalueNN D Ω hn hΩ hc) t
    (summable_heatCoefficient D Ω hn hΩ hc t ht) f

theorem heatKernelL2_sections_integrable_ae (t : ℝ≥0)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    ∀ᵐ x ∂(g.volumeMeasure.restrict Ω),
      Integrable (fun y => heatKernelL2 D Ω hn hΩ hc t (x, y) * f y)
        (g.volumeMeasure.restrict Ω) := by
  let := domainMeasure_isFinite (g := g) Ω hc
  exact Poincare.Analysis.Dirichlet.kernel_sections_integrable_ae _ f



theorem tendsto_heatKernelL2_integral_initial
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    Tendsto (fun t : ℝ≥0 => eLpNorm (fun x =>
      (∫ y, heatKernelL2 D Ω hn hΩ hc t (x, y) * f y
        ∂(g.volumeMeasure.restrict Ω)) - f x) 2 (g.volumeMeasure.restrict Ω))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  have hflow : Tendsto (fun t : ℝ≥0 => heatSemigroup D Ω hn hΩ hc t f)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 f) := by
    simpa only [heatSemigroup_zero, ContinuousLinearMap.id_apply] using
      (continuous_heatSemigroup D Ω hn hΩ hc f).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ≥0) ≤ 𝓝 0)
  have hnorm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun t : ℝ≥0 => heatSemigroup D Ω hn hΩ hc t f) f).mp hflow
  apply hnorm.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply eLpNorm_congr_ae
  filter_upwards [heatKernelL2_integral_ae D Ω hn hΩ hc t ht f] with x hx
  exact congrArg (fun r : ℝ => r - f x) hx

end PoincareConjecture.LeviCivitaData.Dirichlet
