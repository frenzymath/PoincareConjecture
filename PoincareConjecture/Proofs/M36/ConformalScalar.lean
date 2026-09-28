import PoincareConjecture.Proofs.M36.CurvatureTrace
import Mathlib.LinearAlgebra.Basis.SMul

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M36

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem scalarCurvature_positiveScaling_exp
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (F : M → ℝ) (hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling g (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _))) (x : M) :
    D'.scalarCurvature x = Real.exp (2 * F x) *
      (D.scalarCurvature x + 4 * D.laplacian F x -
        2 * g.inner x (D.gradient F x) (D.gradient F x)) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  let b := (g.orthonormalBasis x).reindex (finCongr hdim)
  have hb (i j : Fin 3) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have hlap : (∑ i : Fin 3, D.hessian F x (b i) (b i)) = D.laplacian F x := by
    simp only [b, OrthonormalBasis.reindex_apply, LeviCivitaData.laplacian]
    exact Equiv.sum_comp (finCongr hdim).symm
      (fun i => D.hessian F x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
  have hgrad : (∑ i : Fin 3, (mvfderiv (𝓡 3) F x (b i)) ^ 2) =
      g.inner x (D.gradient F x) (D.gradient F x) := by
    simp_rw [← D.inner_gradient F x]
    exact (b.sum_sq_inner_left (D.gradient F x)).trans
      (real_inner_self_eq_norm_sq (D.gradient F x)).symm
  have hold := scalarCurvature_eq_sum_sectional D x b
  have hnew : D'.scalarCurvature x =
      ∑ i : Fin 3, ∑ j : Fin 3, D'.sectionalCurvature x (b i) (b j) := by
    let a := Real.exp (F x)
    have ha : a ≠ 0 := Real.exp_ne_zero _
    let B := b.toBasis.unitsSMul (fun _ => Units.mk0 a ha)
    have hBval (i : Fin 3) : B i = a • b i := by
      simp [B, Module.Basis.unitsSMul_apply]
    let h := positiveScaling g (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)
    have hexp : Real.exp (-2 * F x) * a * a = 1 := by
      dsimp [a]
      rw [← Real.exp_add, ← Real.exp_add]
      rw [show -2 * F x + F x + F x = 0 by ring, Real.exp_zero]
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨h.toRiemannianMetric⟩
    have hB : Orthonormal ℝ B := by
      apply orthonormal_iff_ite.mpr
      intro i j
      change h.inner x (B i) (B j) = _
      rw [hBval, hBval]
      change Real.exp (-2 * F x) * g.inner x (a • b i) (a • b j) = _
      simp only [map_smul, smul_apply, smul_eq_mul, hb]
      by_cases hij : i = j
      · simp only [if_pos hij, mul_one]
        nlinarith only [hexp]
      · simp [hij]
    let c := B.toOrthonormalBasis hB
    have hc (i : Fin 3) : c i = a • b i := by
      rw [show c i = B i from congrFun (Module.Basis.coe_toOrthonormalBasis B hB) i]
      exact hBval i
    rw [scalarCurvature_eq_sum_sectional D' x c]
    simp only [hc, sectionalCurvature_smul_pair D' x _ _ ha ha]
  have hsec (i j : Fin 3) (hij : i ≠ j) :
      D'.sectionalCurvature x (b i) (b j) = Real.exp (2 * F x) *
        (D.sectionalCurvature x (b i) (b j) +
          D.hessian F x (b i) (b i) + D.hessian F x (b j) (b j) +
          (mvfderiv (𝓡 3) F x (b i)) ^ 2 + (mvfderiv (𝓡 3) F x (b j)) ^ 2 -
          g.inner x (D.gradient F x) (D.gradient F x)) :=
    sectionalCurvature_positiveScaling_exp g D F hF D' x (b i) (b j)
      (b.inner_eq_one i) (b.inner_eq_one j) (b.inner_eq_zero hij)
  rw [hnew, hold]
  simp only [Fin.sum_univ_three, sectionalCurvature_self] at hlap hgrad ⊢
  rw [hsec 0 1 (by decide), hsec 0 2 (by decide), hsec 1 0 (by decide),
    hsec 1 2 (by decide), hsec 2 0 (by decide), hsec 2 1 (by decide)]
  linear_combination (4 * Real.exp (2 * F x)) * hlap +
    (4 * Real.exp (2 * F x)) * hgrad

end PoincareConjecture.M36
