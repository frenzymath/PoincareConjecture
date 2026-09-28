import PoincareConjecture.Proofs.M36.ConformalSectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M60

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem scalarCurvature_conformal_surface
    (g : RiemannianMetric 2 M) (D : LeviCivitaData g)
    (F : M → ℝ) (hF : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (M36.positiveScaling g (fun y => Real.exp (-2 * F y))
      (M36.contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _))) (x : M) :
    D'.scalarCurvature x = Real.exp (2 * F x) *
      (D.scalarCurvature x + 2 * D.laplacian F x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
    simp
  let b := (g.orthonormalBasis x).reindex (finCongr hdim)
  have hb (i j : Fin 2) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have hlap : (∑ i : Fin 2, D.hessian F x (b i) (b i)) = D.laplacian F x := by
    simp only [b, OrthonormalBasis.reindex_apply, LeviCivitaData.laplacian]
    exact Equiv.sum_comp (finCongr hdim).symm
      (fun i => D.hessian F x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
  have hgrad : (∑ i : Fin 2, (mvfderiv (𝓡 2) F x (b i)) ^ 2) =
      g.inner x (D.gradient F x) (D.gradient F x) := by
    simp_rw [← D.inner_gradient F x]
    exact (b.sum_sq_inner_left (D.gradient F x)).trans
      (real_inner_self_eq_norm_sq (D.gradient F x)).symm
  have hsec := M36.sectionalCurvature_positiveScaling_exp g D F hF D' x (b 0) (b 1)
    (b.inner_eq_one 0) (b.inner_eq_one 1) (b.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1))
  have hgram : g.inner x (b 0) (b 0) * g.inner x (b 1) (b 1) -
      (g.inner x (b 0) (b 1)) ^ 2 ≠ 0 := by norm_num [hb]
  have hgram' :
      (M36.positiveScaling g (fun y => Real.exp (-2 * F y))
        (M36.contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)).inner x (b 0) (b 0) *
      (M36.positiveScaling g (fun y => Real.exp (-2 * F y))
        (M36.contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)).inner x (b 1) (b 1) -
      ((M36.positiveScaling g (fun y => Real.exp (-2 * F y))
        (M36.contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)).inner x (b 0) (b 1)) ^ 2 ≠ 0 := by
    simp only [M36.positiveScaling_inner, hb]
    norm_num [Real.exp_ne_zero]
  rw [D.sectionalCurvature_eq_half_scalarCurvature x (b 0) (b 1) hgram,
    D'.sectionalCurvature_eq_half_scalarCurvature x (b 0) (b 1) hgram'] at hsec
  simp only [Fin.sum_univ_two] at hlap hgrad
  linear_combination 2 * hsec + (2 * Real.exp (2 * F x)) * hlap +
    (2 * Real.exp (2 * F x)) * hgrad

end PoincareConjecture.M60
