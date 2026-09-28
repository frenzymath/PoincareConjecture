import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Differential










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem ricciDerivativePairing_surface (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 2) x) :
    ricciDerivativePairing D x u v w =
      mvfderiv (𝓡 2) D.scalarCurvature x u / 2 * g.inner x v w := by
  have hRic : D.ricciEvaluation =
      fun y z => ((1 / 2 : ℝ) * D.scalarCurvature y) * g.inner y (z 0) (z 1) := by
    funext y z
    simp only [ricciEvaluation, D.ricci_eq_half_scalarCurvature_mul_inner]
    ring
  rw [ricciDerivativePairing, hRic,
    D.covariantTensorDerivative_scalar_mul_metric
      (a := fun y => (1 / 2 : ℝ) * D.scalarCurvature y)
      (contMDiff_const.mul D.contMDiff_scalarCurvature)]
  simp only [PoincareConjecture.mvfderiv_const_mul]
  ring

theorem sum_ricciDerivativePairing_surface_divergence (D : LeviCivitaData g)
    (x : M) (v : TangentSpace (𝓡 2) x)
    (e : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x)) :
    (∑ i, ricciDerivativePairing D x (e i) v (e i)) =
      mvfderiv (𝓡 2) D.scalarCurvature x v / 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := congrArg (mvfderiv (𝓡 2) D.scalarCurvature x) (e.sum_repr' v)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simp_rw [D.ricciDerivativePairing_surface]
  calc
    _ = (∑ i, inner ℝ (e i) v * mvfderiv (𝓡 2) D.scalarCurvature x (e i)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      change _ * inner ℝ v (e i) = _
      rw [real_inner_comm v (e i)]
      ring
    _ = _ := by rw [h]

theorem sum_ricciDerivativePairing_surface_trace (D : LeviCivitaData g)
    (x : M) (v : TangentSpace (𝓡 2) x)
    (e : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x)) :
    (∑ i, ricciDerivativePairing D x v (e i) (e i)) =
      mvfderiv (𝓡 2) D.scalarCurvature x v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have he (i : Fin 2) : g.inner x (e i) (e i) = 1 := e.inner_eq_one i
  simp_rw [D.ricciDerivativePairing_surface, he, mul_one]
  simp
  ring



theorem sum_ricciDerivativePairing_surface_index_cancel (D : LeviCivitaData g)
    (x : M) (v : TangentSpace (𝓡 2) x) (s f : ℝ)
    (e : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x)) :
    (∑ i, (-4 * s * ricciDerivativePairing D x (f • e i) v (f • e i) +
      2 * s * ricciDerivativePairing D x v (f • e i) (f • e i))) = 0 := by
  have hfirst (i : Fin 2) :
      ricciDerivativePairing D x (f • e i) v (f • e i) =
        f ^ 2 * ricciDerivativePairing D x (e i) v (e i) := by
    simp only [D.ricciDerivativePairing_surface, map_smul, smul_eq_mul]
    ring
  have hlast (i : Fin 2) :
      ricciDerivativePairing D x v (f • e i) (f • e i) =
        f ^ 2 * ricciDerivativePairing D x v (e i) (e i) := by
    simp only [D.ricciDerivativePairing_surface, map_smul, smul_apply, smul_eq_mul]
    ring
  simp_rw [hfirst, hlast]
  simp only [Finset.sum_add_distrib, ← mul_assoc, ← Finset.mul_sum]
  rw [D.sum_ricciDerivativePairing_surface_divergence,
    D.sum_ricciDerivativePairing_surface_trace]
  ring



theorem sum_surface_indexDensity (D : LeviCivitaData g)
    (x : M) (A : TangentSpace (𝓡 2) x) (s f fp : ℝ)
    (e : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x)) :
    (∑ i, (g.inner x ((fp - s * f * D.scalarCurvature x) • e i)
        ((fp - s * f * D.scalarCurvature x) • e i) +
      D.curvatureTensor x (f • e i) A A (f • e i) +
      2 * s ^ 2 * D.hessian D.scalarCurvature x (f • e i) (f • e i) -
      4 * s * ricciDerivativePairing D x (f • e i) A (f • e i) +
      2 * s * ricciDerivativePairing D x A (f • e i) (f • e i))) =
      2 * fp ^ 2 - 4 * s * f * fp * D.scalarCurvature x +
        f ^ 2 * (2 * s ^ 2 * (D.laplacian D.scalarCurvature x +
          D.scalarCurvature x ^ 2) - D.ricci x A A) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have he (i : Fin 2) : g.inner x (e i) (e i) = 1 := e.inner_eq_one i
  have hnorm (i : Fin 2) :
      g.inner x ((fp - s * f * D.scalarCurvature x) • e i)
        ((fp - s * f * D.scalarCurvature x) • e i) =
      (fp - s * f * D.scalarCurvature x) ^ 2 := by
    simp only [map_smul, smul_apply, smul_eq_mul, he]
    ring
  have hcurv (i : Fin 2) :
      D.curvatureTensor x (f • e i) A A (f • e i) =
        f ^ 2 * D.curvatureTensor x (e i) A A (e i) := by
    rw [D.curvatureTensor_smul_first, D.curvatureTensor_smul_last]
    ring
  have hcurv_trace : (∑ i, D.curvatureTensor x (e i) A A (e i)) =
      -D.ricci x A A := by
    calc
      _ = -(∑ i, D.curvatureTensor x (e i) A (e i) A) := by
        simp_rw [D.curvatureTensor_swap_last x _ A A _]
        rw [Finset.sum_neg_distrib]
      _ = -(∑ i, D.curvatureTensor x (g.orthonormalBasis x i) A
          (g.orthonormalBasis x i) A) := by
        exact congrArg Neg.neg (bilinear_sum_orthonormalBasis_eq
          (D.curvatureTensor_bilinear_first_third x A A) e (g.orthonormalBasis x))
      _ = _ := by
        congr 1
        unfold ricci
        apply Finset.sum_congr rfl
        intro i _
        rw [D.curvatureTensor_swap_first x _ A _ A,
          D.curvatureTensor_swap_last x A _ _ A, neg_neg]
  obtain ⟨H, hH⟩ := (D.hessian_isSmoothCovariantTensor D.contMDiff_scalarCurvature).1 x
  let B := bilinearOfTwoTensor H
  have hB (v w : TangentSpace (𝓡 2) x) :
      D.hessian D.scalarCurvature x v w = B v w := hH ![v, w]
  have hhess (i : Fin 2) :
      D.hessian D.scalarCurvature x (f • e i) (f • e i) =
        f ^ 2 * D.hessian D.scalarCurvature x (e i) (e i) := by
    rw [hB, hB]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hhess_trace : (∑ i, D.hessian D.scalarCurvature x (e i) (e i)) =
      D.laplacian D.scalarCurvature x := by
    simpa only [laplacian, hB] using
      bilinear_sum_orthonormalBasis_eq B e (g.orthonormalBasis x)
  have hcancel := D.sum_ricciDerivativePairing_surface_index_cancel x A s f e
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hcancel
  simp_rw [hnorm, hcurv, hhess]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← mul_assoc, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [hcurv_trace, hhess_trace]
  linear_combination hcancel

end PoincareConjecture.LeviCivitaData
