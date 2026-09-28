import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Order.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.Derivative

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

open Filter Set Bundle Manifold

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem eventually_derivative_bound (g : RiemannianMetric n M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f) (p : M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ y in 𝓝 p, ∀ v,
      |mvfderiv (𝓡 n) f y v| ≤ B * g.tangentNorm y v := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let e := extChartAt (𝓡 n) p
  let F : EuclideanSpace ℝ (Fin n) → ℝ := f ∘ e.symm
  have hF (y : M) (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
      ContDiffAt ℝ ∞ F (e y) := by
    have h := (contMDiffAt_iff_source_of_mem_source hy).mp (hf.contMDiffAt (x := y))
    simpa [F, e, contMDiffWithinAt_iff_contDiffWithinAt, contDiffWithinAt_univ] using h
  have hc := (hF p (mem_chart_source _ p)).continuousAt_fderiv (by simp)
  have hb : ∀ᶠ z in 𝓝 (e p), ‖fderiv ℝ F z‖ < ‖fderiv ℝ F (e p)‖ + 1 :=
    hc.norm.eventually_lt_const (lt_add_one _)
  obtain ⟨C, hC, hchart⟩ := eventually_norm_mfderiv_extChartAt_lt (𝓡 n) p
  refine ⟨(‖fderiv ℝ F (e p)‖ + 1) * C, by positivity, ?_⟩
  have he : ContinuousAt e p := continuousAt_extChartAt p
  filter_upwards [he.eventually hb, hchart,
    chart_source_mem_nhds (EuclideanSpace ℝ (Fin n)) p] with y hy hcy hys
  intro v
  let := normedAddCommGroupTangentSpaceVectorSpace (e y)
  let := normedSpaceTangentSpaceVectorSpace (e y)
  have heq : f =ᶠ[𝓝 y] F ∘ e := by
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hys] with z hz
    dsimp [F]
    rw [e.left_inv (by simpa [e] using hz)]
  have hmd : MDifferentiableAt (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) e y :=
    (contMDiffAt_extChartAt' (n := ∞) hys).mdifferentiableAt (by simp)
  rw [Poincare.mvfderiv_eq_of_eventuallyEq heq,
    mvfderiv_comp y ((hF y hys).differentiableAt (by simp)).mdifferentiableAt hmd]
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
  change |fderiv ℝ F (e y) (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) e y v)| ≤ _
  rw [← Real.norm_eq_abs]
  have hv := (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) e y).le_opNorm v
  have hfv := (fderiv ℝ F (e y)).le_opNorm
    (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) e y v)
  have hn : ‖v‖ = g.tangentNorm y v := rfl
  rw [hn] at hv
  apply hfv.trans
  calc
    ‖fderiv ℝ F (e y)‖ * ‖(mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) e y v :
      EuclideanSpace ℝ (Fin n))‖
      ≤ (‖fderiv ℝ F (e p)‖ + 1) * (C * g.tangentNorm y v) :=
        mul_le_mul hy.le (hv.trans (mul_le_mul_of_nonneg_right hcy.le (Real.sqrt_nonneg _)))
          (norm_nonneg _) (by positivity)
    _ = ((‖fderiv ℝ F (e p)‖ + 1) * C) * g.tangentNorm y v := (mul_assoc _ _ _).symm

theorem exists_metric_derivative_bound_on_compact (g : RiemannianMetric n M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f)
    {S : Set M} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ∀ v,
      |mvfderiv (𝓡 n) f x v| ≤ B * g.tangentNorm x v := by
  classical
  choose B hB hlocal using eventually_derivative_bound g hf
  let U (p : M) := {y | ∀ v, |mvfderiv (𝓡 n) f y v| ≤ B p * g.tangentNorm y v}
  obtain ⟨s, _, hs⟩ := hS.elim_nhds_subcover U (fun p _ ↦ hlocal p)
  refine ⟨∑ p ∈ s, B p, Finset.sum_nonneg (fun p _ ↦ hB p), ?_⟩
  intro x hx v
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact (hxp v).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun q _ ↦ hB q) hp) (Real.sqrt_nonneg _))

theorem exists_metric_derivative_bound_of_hasCompactSupport (g : RiemannianMetric n M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f)
    (hc : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x v,
      |mvfderiv (𝓡 n) f x v| ≤ B * g.tangentNorm x v := by
  obtain ⟨B, hB, hbound⟩ := exists_metric_derivative_bound_on_compact g hf hc
  refine ⟨B, hB, ?_⟩
  intro x v
  by_cases hx : x ∈ tsupport f
  · exact hbound x hx v
  · have heq := notMem_tsupport_iff_eventuallyEq.mp hx
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
    change |mvfderiv (𝓡 n) (fun _ : M ↦ (0 : ℝ)) x v| ≤ _
    simpa only [mvfderiv_const, zero_apply, abs_zero, tangentNorm] using
      mul_nonneg hB (Real.sqrt_nonneg (g.inner x v v))

end PoincareConjecture.RiemannianMetric
