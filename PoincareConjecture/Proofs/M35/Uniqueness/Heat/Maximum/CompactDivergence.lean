import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MovingVolume
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Regularity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem raw_volumeDensity_contDiff (g : RiemannianMetric n V) :
    ContDiff ℝ ∞ (g.pullbackVolumeDensity id) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (g.contDiffAt_pullbackVolumeDensity (f := id) contMDiffAt_id
    (by simpa using Function.injective_id)).1


theorem integral_density_laplacian_eq_zero {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x, g.pullbackVolumeDensity id x * D.laplacian f x) = 0 := by
  let F : Fin n → V → ℝ := fun i x =>
    g.pullbackVolumeDensity id x * WithLp.ofLp (D.gradient f x) i
  have hF (i : Fin n) : ContDiff ℝ ∞ (F i) := by
    apply (raw_volumeDensity_contDiff g).mul
    apply contDiff_iff_contDiffAt.mpr
    intro x
    simpa only [Function.comp_def] using!
      (EuclideanSpace.proj i).contDiff.contDiffAt.comp x
        (D.contDiffAt_gradient_euclidean hf.contDiffAt)
  have hFc (i : Fin n) : HasCompactSupport (F i) := by
    apply hc.mono'
    intro x hx
    by_contra hn
    exact hx (by simp [F, D.gradient_eq_zero_of_notMem_tsupport hn])
  have hI (i : Fin n) : Integrable (fun x =>
      fderiv ℝ (F i) x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (((hF i).continuous_fderiv (by simp)).clm_apply continuous_const
      ).integrable_of_hasCompactSupport ((hFc i).fderiv_apply ℝ _)
  calc
    _ = ∫ x, ∑ i, fderiv ℝ (F i) x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        D.density_mul_laplacian_eq_divergence hf.contDiffAt
    _ = ∑ i, ∫ x, fderiv ℝ (F i) x (EuclideanSpace.basisFun (Fin n) ℝ i) :=
      integral_finsetSum _ (fun i _ => hI i)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (f := fun _ : V => (1 : ℝ)) (g := F i)
        (v := EuclideanSpace.basisFun (Fin n) ℝ i)
        (by simp) (by simpa using hI i)
        (by simpa using (hF i).continuous.integrable_of_hasCompactSupport (hFc i))
        (fun _ _ => differentiableAt_const _) (fun x _ => (hF i).differentiable (by simp) x)
      simpa using h

theorem integrable_density_laplacian {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun x => g.pullbackVolumeDensity id x * D.laplacian f x) :=
  ((raw_volumeDensity_contDiff g).continuous.mul (D.continuous_laplacian hf.contMDiff)
    ).integrable_of_hasCompactSupport ((D.hasCompactSupport_laplacian hc).mul_left)

end PoincareConjecture.M35.Uniqueness.Heat
