import PoincareConjecture.Proofs.M35.Thm12_28.ScalarOperatorPullback
import PoincareConjecture.Proofs.M13.OrdinaryFlow
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Scaling

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35

local notation "E" => EuclideanSpace ℝ (Fin 3)

set_option backward.isDefEq.respectTransparency false in

theorem scale_inverse_metric (g : RiemannianMetric 3 E) (Q : ℝ) (hQ : 0 < Q)
    (x : E) (w : E →L[ℝ] ℝ) :
    ((M13.scaleSmoothMetric g Q hQ).inner x).inverse w = Q⁻¹ • (g.inner x).inverse w := by
  let G : RiemannianMetric 3 E := M13.scaleSmoothMetric g Q hQ
  apply (G.inner_isInvertible x).injective
  rw [(G.inner_isInvertible x).self_apply_inverse]
  ext v
  change w v = Q * (g.inner x (Q⁻¹ • (g.inner x).inverse w) v)
  rw [map_smul, smul_apply, (g.inner_isInvertible x).self_apply_inverse]
  change w v = Q * (Q⁻¹ * w v)
  rw [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul]

theorem scale_gradient {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (f : E → ℝ) (x : E) :
    (M13.scaleLeviCivitaData D Q hQ).gradient f x = Q⁻¹ • D.gradient f x :=
  scale_inverse_metric g Q hQ x (mvfderiv (𝓡 3) f x)

set_option backward.isDefEq.respectTransparency false in

theorem scale_scalarGradientNorm {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (x : E) :
    scalarGradientNorm (M13.scaleSmoothMetric g Q hQ) (M13.scaleLeviCivitaData D Q hQ) x =
      scalarGradientNorm g D x / (Q * Real.sqrt Q) := by
  let DG := M13.scaleLeviCivitaData D Q hQ
  have hscalar : DG.scalarCurvature = fun y => Q⁻¹ * D.scalarCurvature y := by
    funext y
    have h := M13.homothety_scalarCurvature_eq g (M13.scaleSmoothMetric g Q hQ)
      (Diffeomorph.refl (𝓡 3) E ∞) Q hQ (M13.identity_metricHomothety g Q hQ) D DG y
    change DG.scalarCurvature y = D.scalarCurvature y / Q at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hgrad : DG.gradient DG.scalarCurvature x =
      (Q⁻¹ * Q⁻¹) • D.gradient D.scalarCurvature x := by
    rw [hscalar, scale_gradient]
    have hd : mvfderiv (𝓡 3) (fun y => Q⁻¹ * D.scalarCurvature y) x =
        Q⁻¹ • mvfderiv (𝓡 3) D.scalarCurvature x := by
      ext v
      exact mvfderiv_const_mul Q⁻¹ D.scalarCurvature x v
    simp only [LeviCivitaData.gradient, hd, map_smul, smul_smul]
  have hnorm (c : ℝ) (v : E) : g.tangentNorm x (c • v) = |c| * g.tangentNorm x v := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact norm_smul c (show TangentSpace (𝓡 3) x from v)
  rw [scalarGradientNorm_eq_gradient_norm, scalarGradientNorm_eq_gradient_norm]
  change RiemannianMetric.tangentNorm (M13.scaleSmoothMetric g Q hQ) x
    (DG.gradient DG.scalarCurvature x) = _
  rw [M13.scaleSmoothMetric_tangentNorm, hgrad, hnorm,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hQ.le) (inv_nonneg.mpr hQ.le))]
  have hs : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  field_simp
  nlinarith [congrArg (fun a => a * g.tangentNorm x (D.gradient D.scalarCurvature x))
    (Real.sq_sqrt hQ.le)]

set_option backward.isDefEq.respectTransparency false in

theorem scale_laplacian {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) :
    (M13.scaleLeviCivitaData D Q hQ).laplacian f x = Q⁻¹ * D.laplacian f x := by
  let DG := M13.scaleLeviCivitaData D Q hQ
  rw [DG.laplacian_eq_sum_hessian_inverse hf, D.laplacian_eq_sum_hessian_inverse hf,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let u := EuclideanSpace.basisFun (Fin 3) ℝ i
  let v := (g.inner x).inverse (EuclideanSpace.proj i)
  calc
    DG.hessian f x u (((M13.scaleSmoothMetric g Q hQ).inner x).inverse
        (EuclideanSpace.proj i)) =
        fderiv ℝ (fderiv ℝ f) x u (((M13.scaleSmoothMetric g Q hQ).inner x).inverse
          (EuclideanSpace.proj i)) - fderiv ℝ f x
            (CoordinateExponential.christoffelBilinear g.euclideanCoefficients x u
              (((M13.scaleSmoothMetric g Q hQ).inner x).inverse (EuclideanSpace.proj i))) :=
      D.hessian_eq_fderiv_sub_christoffel hf _ _
    _ = Q⁻¹ * (fderiv ℝ (fderiv ℝ f) x u v - fderiv ℝ f x
        (CoordinateExponential.christoffelBilinear g.euclideanCoefficients x u v)) := by
      rw [scale_inverse_metric g Q hQ x (EuclideanSpace.proj i)]
      simp only [map_smul, smul_eq_mul, mul_sub, v]
    _ = Q⁻¹ * D.hessian f x u v :=
      congrArg (fun a : ℝ => Q⁻¹ * a) (D.hessian_eq_fderiv_sub_christoffel hf u v).symm

theorem scale_scalar_laplacian {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (x : E) :
    (M13.scaleLeviCivitaData D Q hQ).laplacian
        (M13.scaleLeviCivitaData D Q hQ).scalarCurvature x =
      D.laplacian D.scalarCurvature x / Q ^ 2 := by
  let DG := M13.scaleLeviCivitaData D Q hQ
  have hscalar : DG.scalarCurvature = fun y => Q⁻¹ * D.scalarCurvature y := by
    funext y
    have h := M13.homothety_scalarCurvature_eq g (M13.scaleSmoothMetric g Q hQ)
      (Diffeomorph.refl (𝓡 3) E ∞) Q hQ (M13.identity_metricHomothety g Q hQ) D DG y
    change DG.scalarCurvature y = D.scalarCurvature y / Q at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  change DG.laplacian DG.scalarCurvature x = _
  rw [hscalar, DG.laplacian_const_mul,
    scale_laplacian D Q hQ (scalarCurvature_contDiffAt_euclidean D x)]
  ring

theorem homothety_ricciNormSq {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace E N] [IsManifold (𝓡 3) ∞ M]
    [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (f : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    D'.ricciNormSq (f x) = D.ricciNormSq x / Q ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f x)) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 3) : N → Type _) (f x)
  let b := g.orthonormalBasis x
  let e := M13.homothetyTangentIsometry g h f Q hQ hf x
  have hnormalized (u v : TangentSpace (𝓡 3) x) :
      D'.ricci (f x) (e u) (e v) = D.ricci x u v / Q := by
    change M13.ricciLinear D' (f x)
      ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 3) (𝓡 3) f x u)
      ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 3) (𝓡 3) f x v) = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, M13.ricciLinear_apply]
    rw [M13.homothety_ricci_eq g h f Q hQ hf D D', ← mul_assoc,
      M13.inv_sqrt_mul_inv_sqrt Q hQ.le]
    ring
  have hnorm : D'.ricciNormSq (f x) =
      ∑ i, ∑ j, (D'.ricci (f x) (e (b i)) (e (b j))) ^ 2 :=
    M13.sum_sq_bilinear_basis_eq (M13.ricciLinear D' (f x))
      (h.orthonormalBasis (f x)) (b.map e)
  rw [hnorm]
  simp only [hnormalized, div_pow, LeviCivitaData.ricciNormSq, Finset.sum_div, b]

theorem scale_ricciNormSq {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (x : E) :
    (M13.scaleLeviCivitaData D Q hQ).ricciNormSq x = D.ricciNormSq x / Q ^ 2 :=
  homothety_ricciNormSq g (M13.scaleSmoothMetric g Q hQ) (Diffeomorph.refl (𝓡 3) E ∞)
    Q hQ (M13.identity_metricHomothety g Q hQ) D (M13.scaleLeviCivitaData D Q hQ) x

theorem scale_scalar_evolution {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (x : E) :
    (M13.scaleLeviCivitaData D Q hQ).laplacian
        (M13.scaleLeviCivitaData D Q hQ).scalarCurvature x +
        2 * (M13.scaleLeviCivitaData D Q hQ).ricciNormSq x =
      (D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x) / Q ^ 2 := by
  rw [scale_scalar_laplacian, scale_ricciNormSq]
  ring

end PoincareConjecture.M35
