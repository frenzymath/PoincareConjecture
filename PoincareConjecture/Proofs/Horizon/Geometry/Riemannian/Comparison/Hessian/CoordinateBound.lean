import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem fderiv2_chart_le_of_hessian_le (D : LeviCivitaData g) (a : M)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ (extChartAt (𝓡 n) a).target)
    {f : M → ℝ}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ((extChartAt (𝓡 n) a).symm z))
    (hgrad : g.inner ((extChartAt (𝓡 n) a).symm z)
      (D.gradient f ((extChartAt (𝓡 n) a).symm z))
      (D.gradient f ((extChartAt (𝓡 n) a).symm z)) = 1)
    {H A G : ℝ} (hH : 0 ≤ H) (hA : 1 ≤ A)
    (hmetric : ‖g.pullbackCoefficients (extChartAt (𝓡 n) a).symm z‖ ≤ A)
    (hchristoffel : ‖CoordinateExponential.christoffelBilinear
      (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm) z‖ ≤ G)
    (hhess : ∀ w : TangentSpace (𝓡 n) ((extChartAt (𝓡 n) a).symm z),
      D.hessian f ((extChartAt (𝓡 n) a).symm z) w w ≤
        H * g.inner ((extChartAt (𝓡 n) a).symm z) w w)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 n) a).symm)) z v v ≤
      (H * A + A * G) * ‖v‖ ^ 2 := by
  let c := extChartAt (𝓡 n) a
  let B := g.pullbackCoefficients c.symm
  let Γ := CoordinateExponential.christoffelBilinear B z
  let T := mfderiv (𝓡 n) (𝓡 n) c.symm z
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hB (w : EuclideanSpace ℝ (Fin n)) :
      g.inner (c.symm z) (T w) (T w) ≤ A * ‖w‖ ^ 2 := by
    change B z w w ≤ _
    have h := (B z).le_opNorm₂ w w
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (by nlinarith [sq_nonneg ‖w‖]))
  have hnorm (w : EuclideanSpace ℝ (Fin n)) :
      g.tangentNorm (c.symm z) (T w) ≤ A * ‖w‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hA0 (norm_nonneg _), (hB w).trans ?_⟩
    have hAA : A ≤ A ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hAA (sq_nonneg ‖w‖)]
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm z :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) a hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  have hfirst (w : EuclideanSpace ℝ (Fin n)) :
      |fderiv ℝ (f ∘ c.symm) z w| ≤ A * ‖w‖ := by
    have heq := congrArg (fun L => L w)
      (mfderiv_comp z (hf.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change fderiv ℝ (f ∘ c.symm) z w = mvfderiv (𝓡 n) f (c.symm z) (T w) at heq
    rw [heq]
    have h := D.abs_mvfderiv_le_gradient_norm f (c.symm z) (T w)
    have hg : g.tangentNorm (c.symm z) (D.gradient f (c.symm z)) = 1 := by
      change Real.sqrt _ = 1
      rw [hgrad, Real.sqrt_one]
    rw [hg, one_mul] at h
    exact h.trans (hnorm w)
  have hΓ : ‖Γ v v‖ ≤ G * ‖v‖ ^ 2 :=
    (Γ.le_opNorm₂ v v).trans (by nlinarith [sq_nonneg ‖v‖])
  have hterm : fderiv ℝ (f ∘ c.symm) z (Γ v v) ≤ A * G * ‖v‖ ^ 2 := by
    exact (le_abs_self _).trans ((hfirst _).trans (by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hΓ hA0))
  have hHess := (hhess (T v)).trans (mul_le_mul_of_nonneg_left (hB v) hH)
  have heq := D.hessian_in_chart a hz hf v v
  change D.hessian f (c.symm z) (T v) (T v) =
    fderiv ℝ (fderiv ℝ (f ∘ c.symm)) z v v -
      fderiv ℝ (f ∘ c.symm) z (Γ v v) at heq
  nlinarith

end PoincareConjecture.LeviCivitaData
