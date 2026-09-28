import PoincareConjecture.Proofs.M35.CapGeometry.CurvatureDerivativeJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.NormContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)

@[instance_reducible] private noncomputable def covectorNormedGroup :
    NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance

attribute [local instance] covectorNormedGroup

@[instance_reducible] private noncomputable def bilinearNormedGroup :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance

attribute [local instance] bilinearNormedGroup

theorem curvatureDerivativeNorm_one_eq_components
    {g : RiemannianMetric 3 V} (D : LeviCivitaData g) (x : V) :
    D.curvatureDerivativeNorm 1 x =
      tensorNormFromComponents
        (Matrix.of (fun i j : Fin 3 => g.inner x
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)))
        (fun a : Fin 5 → Fin 3 => D.covariantTensorDerivative D.riemannEvaluation x
          (fun r => EuclideanSpace.basisFun (Fin 3) ℝ (a r))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : V → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  obtain ⟨A, hA⟩ := (D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_manifold 1).1 x
  have h := tensorNormFromComponents_eq_sqrt_sum A b (g.orthonormalBasis x)
  simp_rw [← hA] at h
  exact h.symm

theorem curvatureDerivativeNorm_one_tendsto_of_metric_jets
    {gseq : ℕ → RiemannianMetric 3 V} {g : RiemannianMetric 3 V}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → V) (p : V)
    (hjet : ∀ m ≤ 3, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => (Dseq k).curvatureDerivativeNorm 1 (pseq k)) atTop
      (𝓝 (D.curvatureDerivativeNorm 1 p)) := by
  have hzero : Tendsto (fun k => (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (g.euclideanCoefficients p)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ V
      (V →L[ℝ] V →L[ℝ] ℝ)).continuous.tendsto _).comp (hjet 0 (by omega))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hmetric (i j : Fin 3) : Tendsto (fun k => (gseq k).inner (pseq k)
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))
      atTop (𝓝 (g.inner p (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j))) := by
    exact ((ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.basisFun (Fin 3) ℝ j)).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ)
        (EuclideanSpace.basisFun (Fin 3) ℝ i)).continuous.tendsto _).comp hzero)
  have hcomponents (a : Fin 5 → Fin 3) : Tendsto
      (fun k => (Dseq k).covariantTensorDerivative (Dseq k).riemannEvaluation (pseq k)
        (fun r => EuclideanSpace.basisFun (Fin 3) ℝ (a r))) atTop
      (𝓝 (D.covariantTensorDerivative D.riemannEvaluation p
        (fun r => EuclideanSpace.basisFun (Fin 3) ℝ (a r)))) := by
    have heq : (fun r => EuclideanSpace.basisFun (Fin 3) ℝ (a r)) =
        ![EuclideanSpace.basisFun (Fin 3) ℝ (a 0),
          EuclideanSpace.basisFun (Fin 3) ℝ (a 1),
          EuclideanSpace.basisFun (Fin 3) ℝ (a 2),
          EuclideanSpace.basisFun (Fin 3) ℝ (a 3),
          EuclideanSpace.basisFun (Fin 3) ℝ (a 4)] := by
      funext r
      fin_cases r <;> rfl
    rw [heq]
    exact covariantCurvatureDerivative_tendsto_of_metric_jets Dseq D pseq p _ _ _ _ _ hjet
  have hdet : (Matrix.of (fun i j : Fin 3 => g.inner p
      (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j))).det ≠ 0 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : V → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let b : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) p) :=
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    change (Matrix.gram ℝ b).det ≠ 0
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  simp_rw [curvatureDerivativeNorm_one_eq_components]
  exact tendsto_tensorNormFromComponents hmetric hcomponents hdet

end PoincareConjecture.M35
