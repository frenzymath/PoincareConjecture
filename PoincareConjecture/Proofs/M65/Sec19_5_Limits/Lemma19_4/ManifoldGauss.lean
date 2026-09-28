import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ChartMetricRealization
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussTransport

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M65Gauss

variable {m n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))}

theorem exists_chart_gauss_curvatureTensor
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : EuclideanSpace ℝ (Fin m) → M} {x : EuclideanSpace ℝ (Fin m)}
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt (𝓡 m) (𝓡 n) ∞ f y)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin m),
      h.inner y u v = g.inner (f y)
        (mfderiv (𝓡 m) (𝓡 n) f y u) (mfderiv (𝓡 m) (𝓡 n) f y v)) :
    let c := extChartAt (𝓡 n) (f x)
    let G := c ∘ f
    ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE),
      (∀ᶠ y in 𝓝 (G x), ∀ u v : EuclideanSpace ℝ (Fin n),
        gE.inner y u v = g.inner (c.symm y)
          (mfderiv (𝓡 n) (𝓡 n) c.symm y u) (mfderiv (𝓡 n) (𝓡 n) c.symm y v)) ∧
      ∀ u v w z : EuclideanSpace ℝ (Fin m),
        D'.curvatureTensor x u v w z =
          D.curvatureTensor (f x)
            (mfderiv (𝓡 m) (𝓡 n) f x u) (mfderiv (𝓡 m) (𝓡 n) f x v)
            (mfderiv (𝓡 m) (𝓡 n) f x w) (mfderiv (𝓡 m) (𝓡 n) f x z) +
          g.inner (f x)
            (mfderiv (𝓡 n) (𝓡 n) c.symm (G x) (secondFundamentalForm DE D' G x u w))
            (mfderiv (𝓡 n) (𝓡 n) c.symm (G x) (secondFundamentalForm DE D' G x v z)) -
          g.inner (f x)
            (mfderiv (𝓡 n) (𝓡 n) c.symm (G x) (secondFundamentalForm DE D' G x u z))
            (mfderiv (𝓡 n) (𝓡 n) c.symm (G x) (secondFundamentalForm DE D' G x v w)) := by
  let c := extChartAt (𝓡 n) (f x)
  let G := c ∘ f
  have hsrc : ∀ᶠ y in 𝓝 x, f y ∈ c.source :=
    hf.self_of_nhds.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := 𝓡 n) (f x))
  have hG : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ G y := by
    filter_upwards [hf, hsrc] with y hfy hy
    have hy' : f y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (f x)).source := by
      simpa only [c, extChartAt_source] using hy
    exact contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt' hy').comp y hfy)
  have hψ : ∀ᶠ y in 𝓝 (G x), ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target (f x))] with y hy
    exact (contMDiffWithinAt_extChartAt_symm_target (n := ∞) (f x) hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hinv : ∀ᶠ y in 𝓝 (G x), (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target (f x))] with y hy
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  have hcomp : c.symm ∘ G =ᶠ[𝓝 x] f := by
    filter_upwards [hsrc] with y hy
    exact c.left_inv hy
  have hmetric' : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin m),
      h.inner y u v = g.inner ((c.symm ∘ G) y)
        (mfderiv (𝓡 m) (𝓡 n) (c.symm ∘ G) y u)
        (mfderiv (𝓡 m) (𝓡 n) (c.symm ∘ G) y v) := by
    filter_upwards [hmetric, hcomp.eventually_nhds] with y hy heq u v
    change c.symm ∘ G =ᶠ[𝓝 y] f at heq
    rw [heq.self_of_nhds, heq.mfderiv_eq]
    exact hy u v
  obtain ⟨gE, DE, hE⟩ := m65Exists_chartMetric g (f x)
  refine ⟨gE, DE, hE, fun u v w z => ?_⟩
  have h := gauss_curvatureTensor_transport D DE D' hG hψ hinv hE hmetric' u v w z
  have hpoint : (c.symm ∘ G) x = f x := hcomp.self_of_nhds
  rw [hpoint, hcomp.mfderiv_eq] at h
  exact h

end PoincareConjecture.M65Gauss
