import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Derivatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_terminal_scalar_time_constant
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M] (J : Set ℝ)
        (F : RicciFlow (m + 1) M J),
        Icc (-2 : ℝ) 0 ⊆ interior J →
        (∀ t ∈ Icc (-2 : ℝ) 0, MetricComplete (F.metric t)) →
        (∀ t ∈ Icc (-2 : ℝ) 0, ∀ x : M,
          (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M,
          (∀ t ∈ Icc (-2 : ℝ) 0,
            ∀ x ∈ (F.metric 0).ball p (64 * (((m + 1 : ℕ) : ℝ) + 8)),
              (F.connection t).scalarCurvature x ≤ 4) →
          ∀ t ∈ Icc (-1 : ℝ) 0,
            (F.connection 0).scalarCurvature p - (F.connection t).scalarCurvature p ≤
              D * (0 - t) := by
  let N : ℝ := (m + 1 : ℕ)
  have hN : 0 < N := by dsimp only [N]; positivity
  obtain ⟨C, hCpos, hShi⟩ := exists_terminal_cylinder_derivative_constant hC hm 2
    (S := 4) (A := 2 * (N ^ 2 * 4)) (r := 64 * (N + 8)) (scale := 1)
    (by norm_num) (by positivity) (by positivity) (by norm_num)
  let D := N ^ 3 * C + 32
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro M _ _ _ _ _ J F hJ hcomplete hoperator p hscalar t ht
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  have htime : (0 : ℝ) - (-2) ≤ (2 * (N ^ 2 * 4)) / (N ^ 2 * 4) := by
    rw [mul_div_cancel_right₀ _ (by positivity : N ^ 2 * 4 ≠ 0)]
    norm_num
  have hgap : (64 * (N + 8)) / 4 + (4 * N * 1 + 8 * 4 / 1) * (0 - (-2)) <
      (64 * (N + 8)) / 2 := by nlinarith
  have hderiv (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) :
      (F.connection s).curvatureDerivativeNorm 2 p ≤ C := by
    have h := hShi M J F (-2) 0 (by norm_num) hJ hcomplete hoperator p htime
      hgap hscalar s ⟨by linarith [hs.1], hs.2⟩ p
      (by simp [RiemannianMetric.edist, Manifold.riemannianEDist_self])
    norm_num at h
    exact h.trans (div_le_self hCpos.le (by linarith [hs.1]))
  have hp : p ∈ (F.metric 0).ball p (64 * (N + 8)) := by
    change (F.metric 0).edist p p < ENNReal.ofReal (64 * (N + 8))
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self, ENNReal.ofReal_pos]
    positivity
  have hsub : Icc (-1 : ℝ) 0 ⊆ Icc (-2 : ℝ) 0 := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hdiff (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) :
      DifferentiableAt ℝ (fun q => (F.connection q).scalarCurvature p) s :=
    ((hC.scalar_evolution (m + 1) M J F s (interior_subset (hJ (hsub hs))) p).hasDerivAt
      (mem_interior_iff_mem_nhds.mp (hJ (hsub hs)))).differentiableAt
  have hslope (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) :
      deriv (fun q => (F.connection q).scalarCurvature p) s ≤ D := by
    have hcalc := hC.tensor_calculus (m + 1) M (F.metric s) (F.connection s)
    have hnonneg := ((F.connection s).curvatureOperatorBound_scalarCurvature
      hcalc p (hoperator s (hsub hs) p)).1
    have hupper := hscalar s (hsub hs) p hp
    have hlap := ((F.connection s).abs_laplacian_scalar_le_curvatureDerivativeNorm hcalc p).trans
      (mul_le_mul_of_nonneg_left (hderiv s hs) (by positivity))
    have hevol := F.deriv_scalarCurvature_le_laplacian_add_sq_of_nonnegative_curvatureOperator
      hC (hJ (hsub hs)) p (hoperator s (hsub hs) p)
    dsimp only [D, N] at *
    nlinarith [le_abs_self ((F.connection s).laplacian (F.connection s).scalarCurvature p)]
  exact (convex_Icc (-1 : ℝ) 0).image_sub_le_mul_sub_of_deriv_le
    (fun s hs => (hdiff s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hdiff s (interior_subset hs)).differentiableWithinAt)
    (fun s hs => hslope s (interior_subset hs)) t ht 0 (by norm_num) ht.2

end PoincareConjecture.RicciFlow
