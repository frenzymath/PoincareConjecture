import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Equation.Entropy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.GradientEnergyTime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.LaplacianTime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Bochner








set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem laplacian_drift_of_potentialResidual (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ} (ht : t ∈ interior J)
    (hf : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (univ ×ˢ J))
    (hpde : ∀ y, F.potentialResidual f t y = 0) (x : M) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let φ := fun y ↦ f (y, t)
    deriv (fun s ↦ (F.connection s).laplacian (fun y ↦ f (y, s)) x) t +
        D.spatialDrift φ (D.laplacian φ) x =
      2 * (∑ i, ∑ j, (D.hessian φ x (b i) (b j)) ^ 2) +
        2 * D.ricci x (D.gradient φ x) (D.gradient φ x) +
        2 * (∑ i, ∑ j, D.ricci x (b i) (b j) * D.hessian φ x (b i) (b j)) -
        D.laplacian D.scalarCurvature x := by
  let D := F.connection t
  let φ := fun y ↦ f (y, t)
  let N := fun y ↦ (F.metric t).inner y (D.gradient φ y) (D.gradient φ y)
  have hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ :=
    contMDiffOn_univ.mp (hf.comp (contMDiffOn_id.prodMk contMDiffOn_const)
      (fun y _ ↦ ⟨mem_univ y, interior_subset ht⟩))
  have hN := D.contMDiff_inner_gradient hφ hφ
  have hL := D.contMDiff_laplacian hφ
  have hR := D.contMDiff_scalarCurvature
  have heq : (fun y ↦ deriv (fun s ↦ f (y, s)) t) =
      (fun y ↦ (N y - D.scalarCurvature y) - D.laplacian φ y + n / (2 * -t)) := by
    funext y
    have h := hpde y
    dsimp only [potentialResidual] at h
    dsimp only [N, D, φ]
    linarith
  have htime := (F.hasDerivAt_laplacian ht hf x).deriv
  dsimp only at htime ⊢
  rw [heq, D.laplacian_add ((hN.sub hR).sub hL) contMDiff_const,
    D.laplacian_sub (hN.sub hR) hL, D.laplacian_sub hN hR] at htime
  have hc : D.laplacian (fun _ : M ↦ (n : ℝ) / (2 * -t)) x = 0 := by
    simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const]
  rw [hc] at htime
  have hb := D.bochner_identity hφ x
  dsimp only [LeviCivitaData.spatialDrift, D, φ, N] at htime hb ⊢
  linarith

theorem gradientEnergy_drift_of_potentialResidual (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ} (ht : t ∈ interior J)
    (hf : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (univ ×ˢ J))
    (hpde : ∀ y, F.potentialResidual f t y = 0) (x : M) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let φ := fun y ↦ f (y, t)
    let N := fun y ↦ (F.metric t).inner y (D.gradient φ y) (D.gradient φ y)
    deriv (fun s ↦ (F.metric s).inner x
        ((F.connection s).gradient (fun y ↦ f (y, s)) x)
        ((F.connection s).gradient (fun y ↦ f (y, s)) x)) t +
      D.spatialDrift φ N x =
        2 * (∑ i, ∑ j, (D.hessian φ x (b i) (b j)) ^ 2) +
        4 * D.ricci x (D.gradient φ x) (D.gradient φ x) -
        2 * mvfderiv (𝓡 n) D.scalarCurvature x (D.gradient φ x) := by
  let D := F.connection t
  let φ := fun y ↦ f (y, t)
  let N := fun y ↦ (F.metric t).inner y (D.gradient φ y) (D.gradient φ y)
  have hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ :=
    contMDiffOn_univ.mp (hf.comp (contMDiffOn_id.prodMk contMDiffOn_const)
      (fun y _ ↦ ⟨mem_univ y, interior_subset ht⟩))
  have hN := D.contMDiff_inner_gradient hφ hφ
  have hL := D.contMDiff_laplacian hφ
  have hR := D.contMDiff_scalarCurvature
  have heq : (fun y ↦ deriv (fun s ↦ f (y, s)) t) =
      (fun y ↦ (N y - D.scalarCurvature y) - D.laplacian φ y + n / (2 * -t)) := by
    funext y
    have h := hpde y
    dsimp only [potentialResidual] at h
    dsimp only [N, D, φ]
    linarith
  have htime := (F.hasDerivAt_gradient_normSq ht hf x).deriv
  rw [(F.metric t).symm x _ ((F.connection t).gradient
      (fun y ↦ deriv (fun s ↦ f (y, s)) t) x), D.inner_gradient, heq,
    mvfderiv_fun_add ((((hN.sub hR).sub hL) x).mdifferentiableAt (by simp))
      mdifferentiableAt_const,
    mvfderiv_fun_sub (((hN.sub hR) x).mdifferentiableAt (by simp))
      ((hL x).mdifferentiableAt (by simp)),
    mvfderiv_fun_sub ((hN x).mdifferentiableAt (by simp))
      ((hR x).mdifferentiableAt (by simp))] at htime
  simp only [sub_apply, mvfderiv_const, add_zero] at htime
  have hb := D.bochner_identity hφ x
  dsimp only [LeviCivitaData.spatialDrift, D, φ, N] at htime hb ⊢
  linarith

end PoincareConjecture.RicciFlow
