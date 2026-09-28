import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.PotentialRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Differential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.ContractedBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Constancy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators
open Bundle

noncomputable section

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem mvfderiv_scalarCurvature_of_C2_gradient_soliton
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 n) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) D.scalarCurvature x v = 2 * D.ricci x (D.gradient f x) v := by
  have hfs := D.contMDiff_of_C2_gradient_soliton hf hsol
  have hH : ∀ a b c : TangentSpace (𝓡 n) x,
      D.covariantTensorDerivative (fun y w => D.hessian f y (w 0) (w 1)) x ![a, b, c] =
        -D.covariantTensorDerivative D.ricciEvaluation x ![a, b, c] := by
    intro a b c
    have heq : (fun y (w : Fin 2 → TangentSpace (𝓡 n) y) =>
        D.ricciEvaluation y w + D.hessian f y (w 0) (w 1)) =
          (fun y w => lambda * g.inner y (w 0) (w 1)) := by
      funext y w
      exact hsol y (w 0) (w 1)
    have hd := congrArg (fun T => D.covariantTensorDerivative T x ![a, b, c]) heq
    rw [D.covariantTensorDerivative_add D.ricciEvaluation_isSmooth_manifold
      (D.hessian_isSmoothCovariantTensor hfs),
      D.covariantTensorDerivative_scalar_mul_metric (a := fun _ : M => lambda)
        contMDiff_const] at hd
    simp only [mvfderiv_const, zero_apply, zero_mul] at hd
    rw [add_comm] at hd
    exact eq_neg_of_add_eq_zero_left hd
  let b := g.orthonormalBasis x
  have hpair (a c : TangentSpace (𝓡 n) x) : D.ricci x a c = D.ricci x c a :=
    (hD.2.2.2.1 x a c c a).2.2.2
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      mvfderiv (𝓡 n) D.scalarCurvature x (b i) =
        2 * D.ricci x (D.gradient f x) (b i) := by
    have hterm (j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :=
      D.covariantTensorDerivative_hessian_commutator hfs x (b j) (b i) (b j)
    have hcurv (j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
        -mvfderiv (𝓡 n) f x (D.curvature x (b j) (b i) (b j)) =
          D.curvatureTensor x (b i) (b j) (D.gradient f x) (b j) := by
      rw [← D.inner_gradient, g.symm]
      change -D.curvatureTensor x (b j) (b i) (D.gradient f x) (b j) = _
      rw [D.curvatureTensor_swap_first, neg_neg]
    simp_rw [hH, hcurv] at hterm
    have hsum := congrArg (fun F : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ =>
      ∑ j, F j) (funext hterm)
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsum
    change -(∑ j, D.frameRicciDerivative x j i j) -
        -(∑ j, D.frameRicciDerivative x i j j) = D.ricci x (b i) (D.gradient f x) at hsum
    rw [D.frameRicciDerivative_trace hD, D.frameRicciDerivative_scalar_trace hD,
      hpair] at hsum
    change -(mvfderiv (𝓡 n) D.scalarCurvature x (b i) / 2) -
      -mvfderiv (𝓡 n) D.scalarCurvature x (b i) = _ at hsum
    linarith only [hsum]
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x (b i) (b i)
  have hB (a c : TangentSpace (𝓡 n) x) : B a c = D.ricci x a c := by
    simp [B, ricci, b, LinearMap.sum_apply]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hv : v = ∑ i, (b.repr v i) • b i := (b.sum_repr v).symm
  rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul, hb]
  rw [← hB, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hB]; ring)

theorem exists_hamilton_conservation_of_C2_gradient_soliton [PreconnectedSpace M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 n) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w) :
    ∃ C : ℝ, ∀ x, D.scalarCurvature x +
      g.inner x (D.gradient f x) (D.gradient f x) - 2 * lambda * f x = C := by
  have hfs := D.contMDiff_of_C2_gradient_soliton hf hsol
  have hnorm : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (D.gradient f x) (D.gradient f x)) := by
    intro x
    have hgrad := D.contMDiffAt_gradient (hfs x)
    simpa using (contMDiffAt_totalSpace.mp
      (((g.contMDiff x).clm_bundle_apply hgrad).clm_bundle_apply hgrad)).2
  have hcont : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => D.scalarCurvature x +
        g.inner x (D.gradient f x) (D.gradient f x) - 2 * lambda * f x) :=
    (D.contMDiff_scalarCurvature.add hnorm).sub (contMDiff_const.mul hfs)
  apply Poincare.Manifold.exists_eq_const_of_mvfderiv_eq_zero
    (fun x => (hcont x).mdifferentiableAt (by simp))
  intro x v
  rw [mvfderiv_fun_sub
    (g := fun y => D.scalarCurvature y + g.inner y (D.gradient f y) (D.gradient f y))
    (g' := fun y => 2 * lambda * f y)
    (((D.contMDiff_scalarCurvature x).add (hnorm x)).mdifferentiableAt (by simp))
    (((contMDiffAt_const (c := 2 * lambda)).mul (hfs x)).mdifferentiableAt (by simp)),
    mvfderiv_fun_add ((D.contMDiff_scalarCurvature x).mdifferentiableAt (by simp))
      ((hnorm x).mdifferentiableAt (by simp))]
  simp only [sub_apply, add_apply, PoincareConjecture.mvfderiv_const_mul]
  rw [D.mvfderiv_scalarCurvature_of_C2_gradient_soliton hD hf hsol,
    D.mvfderiv_gradient_normSq_of_C2 (hf x)]
  have hsym := (hD.2.2.2.1 x v (D.gradient f x) (D.gradient f x) v).2.2.2
  have heq := hsol x v (D.gradient f x)
  rw [g.symm x v, D.inner_gradient] at heq
  linarith only [heq, hsym]

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem mvfderiv_scalarCurvature_threeDimensional
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus)
    (x : M) (v : TangentSpace (𝓡 3) x) :
    mvfderiv (𝓡 3) S.connection.scalarCurvature x v =
      2 * S.connection.ricci x (S.connection.gradient S.potential x) v :=
  S.connection.mvfderiv_scalarCurvature_of_C2_gradient_soliton hD
    S.potential_C2 S.soliton_equation x v

theorem exists_hamilton_conservation_threeDimensional
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus) :
    ∃ C : ℝ, ∀ x, S.connection.scalarCurvature x +
      S.metric.inner x (S.connection.gradient S.potential x)
        (S.connection.gradient S.potential x) - S.potential x = C := by
  simpa using S.connection.exists_hamilton_conservation_of_C2_gradient_soliton hD
    S.potential_C2 S.soliton_equation

end PoincareConjecture.GradientShrinkingSolitonData
