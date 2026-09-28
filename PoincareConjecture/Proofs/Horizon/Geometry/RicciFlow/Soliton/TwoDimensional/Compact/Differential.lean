import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Regularity.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Commutation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem covariantTensorDerivative_scalar_mul_metric (D : LeviCivitaData g)
    {a : M → ℝ} (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a)
    (x : M) (v b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y w => a y * g.inner y (w 0) (w 1)) x ![v, b, c] =
      mvfderiv (𝓡 n) a x v * g.inner x b c := by
  have hb := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) b
  have hc := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) c
  have hinner := ((g.contMDiff x).clm_bundle_apply hb).clm_bundle_apply hc
  have hinner' : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b y)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) c y)) x := by
    simpa using (contMDiffAt_totalSpace.mp hinner).2
  have hprod := mvfderiv_fun_mul ((ha x).mdifferentiableAt (by simp))
    (hinner'.mdifferentiableAt (by simp))
  have hg := D.mvfderiv_metric_extend x v b c
  simp only [covariantTensorDerivative, Fin.sum_univ_two]
  simp
  rw [hprod]
  simp only [add_apply, smul_apply,
    smul_eq_mul, FiberBundle.extend_apply_self]
  rw [hg]
  ring

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem hessian_eq_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ}
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (x : M) (v w : TangentSpace (𝓡 2) x) :
    D.hessian f x v w = (lambda - (1 / 2 : ℝ) * D.scalarCurvature x) * g.inner x v w := by
  have h := hsol x v w
  rw [D.ricci_eq_half_scalarCurvature_mul_inner] at h
  linarith

theorem contMDiff_of_C2_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f := by
  apply D.contMDiff_of_C2_hessian_eq_smooth_mul_metric hf
    (a := fun x => lambda - (1 / 2 : ℝ) * D.scalarCurvature x)
  · exact contMDiff_const.sub (contMDiff_const.mul D.contMDiff_scalarCurvature)
  · exact D.hessian_eq_of_surface_soliton hsol

theorem mvfderiv_scalarCurvature_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (x : M) (v : TangentSpace (𝓡 2) x) :
    mvfderiv (𝓡 2) D.scalarCurvature x v =
      D.scalarCurvature x * mvfderiv (𝓡 2) f x v := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  let a := fun y => lambda - (1 / 2 : ℝ) * D.scalarCurvature y
  have ha : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ a :=
    contMDiff_const.sub (contMDiff_const.mul D.contMDiff_scalarCurvature)
  have heq : (fun y (w : Fin 2 → TangentSpace (𝓡 2) y) => D.hessian f y (w 0) (w 1)) =
      (fun y w => a y * g.inner y (w 0) (w 1)) := by
    funext y w
    exact D.hessian_eq_of_surface_soliton hsol y (w 0) (w 1)
  have hda (w : TangentSpace (𝓡 2) x) :
      mvfderiv (𝓡 2) a x w = -(1 / 2 : ℝ) * mvfderiv (𝓡 2) D.scalarCurvature x w := by
    dsimp only [a]
    rw [mvfderiv_fun_sub (g := fun _ : M => lambda)
      (g' := fun y => (1 / 2 : ℝ) * D.scalarCurvature y) mdifferentiableAt_const
      ((contMDiff_const.mul D.contMDiff_scalarCurvature x).mdifferentiableAt (by simp))]
    simp [PoincareConjecture.mvfderiv_const_mul, mvfderiv_const]
  have hcomm (u w z : TangentSpace (𝓡 2) x) :=
    D.covariantTensorDerivative_hessian_commutator hfs x u w z
  simp_rw [heq, D.covariantTensorDerivative_scalar_mul_metric ha, hda] at hcomm
  have hcurv (u w z : TangentSpace (𝓡 2) x) :
      mvfderiv (𝓡 2) f x (D.curvature x u w z) =
        D.scalarCurvature x / 2 *
          (mvfderiv (𝓡 2) f x u * g.inner x w z -
            g.inner x u z * mvfderiv (𝓡 2) f x w) := by
    rw [← D.inner_gradient, g.symm]
    change D.curvatureTensor x u w (D.gradient f x) z = _
    rw [D.curvatureTensor_eq_half_scalarCurvature]
    rw [g.symm x u (D.gradient f x), g.symm x w (D.gradient f x),
      D.inner_gradient, D.inner_gradient]
  simp_rw [hcurv] at hcomm
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  let b : OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x) :=
    (g.orthonormalBasis x).reindex (finCongr hd)
  have hb (i j : Fin 2) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have hframe (i : Fin 2) : mvfderiv (𝓡 2) D.scalarCurvature x (b i) =
      D.scalarCurvature x * mvfderiv (𝓡 2) f x (b i) := by
    fin_cases i
    · have h := hcomm (b 0) (b 1) (b 1)
      norm_num [hb] at h
      change mvfderiv (𝓡 2) D.scalarCurvature x (b 0) =
        D.scalarCurvature x * mvfderiv (𝓡 2) f x (b 0)
      linear_combination 2 * h
    · have h := hcomm (b 1) (b 0) (b 0)
      norm_num [hb] at h
      change mvfderiv (𝓡 2) D.scalarCurvature x (b 1) =
        D.scalarCurvature x * mvfderiv (𝓡 2) f x (b 1)
      linear_combination 2 * h
  have hlinear : (mvfderiv (𝓡 2) D.scalarCurvature x).toLinearMap =
      (D.scalarCurvature x • mvfderiv (𝓡 2) f x).toLinearMap := by
    apply b.toBasis.ext
    exact hframe
  exact congrArg (fun L => L v) hlinear

theorem mvfderiv_hamilton_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (x : M) (v : TangentSpace (𝓡 2) x) :
    mvfderiv (𝓡 2) (fun y => D.scalarCurvature y +
      g.inner y (D.gradient f y) (D.gradient f y) - 2 * lambda * f y) x v = 0 := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  have hgrad := D.contMDiffAt_gradient (hfs x)
  have hnorm : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x := by
    simpa using (contMDiffAt_totalSpace.mp
      (((g.contMDiff x).clm_bundle_apply hgrad).clm_bundle_apply hgrad)).2
  rw [mvfderiv_fun_sub
    (g := fun y => D.scalarCurvature y + g.inner y (D.gradient f y) (D.gradient f y))
    (g' := fun y => 2 * lambda * f y)
    (((D.contMDiff_scalarCurvature x).add hnorm).mdifferentiableAt (by simp))
    (((contMDiffAt_const (c := 2 * lambda)).mul (hfs x)).mdifferentiableAt (by simp)),
    mvfderiv_fun_add ((D.contMDiff_scalarCurvature x).mdifferentiableAt (by simp))
      (hnorm.mdifferentiableAt (by simp))]
  simp only [sub_apply, add_apply, PoincareConjecture.mvfderiv_const_mul]
  rw [D.mvfderiv_scalarCurvature_of_surface_soliton hf hsol,
    D.mvfderiv_gradient_normSq_of_C2 (hf x), D.hessian_eq_of_surface_soliton hsol,
    g.symm x v, D.inner_gradient]
  ring

theorem mvfderiv_weighted_scalar_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (x : M) (v : TangentSpace (𝓡 2) x) :
    mvfderiv (𝓡 2) (fun y => D.scalarCurvature y * Real.exp (-f y)) x v = 0 := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  have hexp : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => Real.exp (-f y)) :=
    Real.contDiff_exp.contMDiff.comp hfs.neg
  have hdexp : mvfderiv (𝓡 2) (fun y => Real.exp (-f y)) x v =
      -Real.exp (-f x) * mvfderiv (𝓡 2) f x v := by
    change mvfderiv (𝓡 2) (Real.exp ∘ fun y => -f y) x v = _
    rw [mvfderiv_comp x Real.differentiableAt_exp.mdifferentiableAt
      ((hfs.neg x).mdifferentiableAt (by simp))]
    simp only [ContinuousLinearMap.comp_apply, mvfderiv, mfderiv_eq_fderiv]
    rw [(Real.hasDerivAt_exp (-f x)).hasFDerivAt.fderiv]
    change mvfderiv (𝓡 2) (-f) x v * Real.exp (-f x) =
      -Real.exp (-f x) * mvfderiv (𝓡 2) f x v
    rw [mvfderiv_neg (g := f)]
    simp only [neg_apply]
    ring
  rw [mvfderiv_fun_mul ((D.contMDiff_scalarCurvature x).mdifferentiableAt (by simp))
    ((hexp x).mdifferentiableAt (by simp))]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hdexp, D.mvfderiv_scalarCurvature_of_surface_soliton hf hsol]
  ring

end PoincareConjecture.LeviCivitaData
