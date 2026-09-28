import PoincareConjecture.Proofs.M35.CapGeometry.RadialSectionalDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality

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

private theorem extend_const (x v y : V) :
    FiberBundle.extend V (E := TangentSpace (𝓡 3)) (x := x) v y = v := by
  simp only [FiberBundle.extend, trivializationAt_model_space_apply]
  have h := (trivializationAt V (TangentSpace (𝓡 3)) x).symmL_apply
    (R := ℝ) (b := y) (by change y ∈ Set.univ; trivial) (y := v)
  simp only [TangentBundle.symmL_model_space] at h
  exact h.symm

private theorem curvature_derivative_const
    {g : RiemannianMetric 3 V} (D : LeviCivitaData g) (x u a b c d : V) :
    D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d] =
      fderiv ℝ (fun y => D.curvatureTensor y a b c d) x u -
        (D.curvatureTensor x (D.euclideanConnection u a x) b c d +
          D.curvatureTensor x a (D.euclideanConnection u b x) c d +
          D.curvatureTensor x a b (D.euclideanConnection u c x) d +
          D.curvatureTensor x a b c (D.euclideanConnection u d x)) := by
  have he (v : V) :
      FiberBundle.extend V (E := TangentSpace (𝓡 3)) (x := x) v = fun _ => v :=
    funext (extend_const x v)
  rw [D.covariantTensorDerivative_riemannEvaluation_eq]
  dsimp only
  rw [he, he, he, he, mvfderiv, mfderiv_eq_fderiv]
  rfl

private theorem linear_eval_tendsto
    (Lseq : ℕ → V →ₗ[ℝ] ℝ) (L : V →ₗ[ℝ] ℝ)
    {vseq : ℕ → V} {v : V} (hv : Tendsto vseq atTop (𝓝 v))
    (hL : ∀ i : Fin 3, Tendsto
      (fun k => Lseq k (EuclideanSpace.basisFun (Fin 3) ℝ i)) atTop
      (𝓝 (L (EuclideanSpace.basisFun (Fin 3) ℝ i)))) :
    Tendsto (fun k => Lseq k (vseq k)) atTop (𝓝 (L v)) := by
  have heq (A : V →ₗ[ℝ] ℝ) (w : V) :
      A w = ∑ i : Fin 3, w i * A (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
    have hw : (∑ i : Fin 3, w i • EuclideanSpace.basisFun (Fin 3) ℝ i) = w := by
      simpa only [EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
    conv_lhs => rw [← hw, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hseq : (fun k => Lseq k (vseq k)) =
      (fun k => ∑ i : Fin 3, vseq k i * Lseq k (EuclideanSpace.basisFun (Fin 3) ℝ i)) :=
    funext (fun k => heq (Lseq k) (vseq k))
  rw [hseq, heq L v]
  apply tendsto_finsetSum
  intro i _
  exact (((EuclideanSpace.proj i : V →L[ℝ] ℝ).continuous.tendsto v).comp hv).mul (hL i)

theorem covariantCurvatureDerivative_tendsto_of_metric_jets
    {gseq : ℕ → RiemannianMetric 3 V} {g : RiemannianMetric 3 V}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → V) (p u a b c d : V)
    (hjet : ∀ m ≤ 3, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => (Dseq k).covariantTensorDerivative (Dseq k).riemannEvaluation
      (pseq k) ![u, a, b, c, d]) atTop
      (𝓝 (D.covariantTensorDerivative D.riemannEvaluation p ![u, a, b, c, d])) := by
  have hcurv (v₁ v₂ v₃ v₄ : V) :
      Tendsto (fun k => (Dseq k).curvatureTensor (pseq k) v₁ v₂ v₃ v₄) atTop
        (𝓝 (D.curvatureTensor p v₁ v₂ v₃ v₄)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ V ℝ).continuous.tendsto _).comp
      (curvatureTensor_jets_tendsto_of_metric_jets Dseq D pseq p v₁ v₂ v₃ v₄ 0
        (fun m hm => hjet m (by omega)))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hconn (v w : V) :
      Tendsto (fun k => (Dseq k).euclideanConnection v w (pseq k)) atTop
        (𝓝 (D.euclideanConnection v w p)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ V V).continuous.tendsto _).comp
      (euclideanConnection_jets_tendsto_of_metric_jets Dseq D pseq p v w 0
        (fun m hm => hjet m (by omega)))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hderiv : Tendsto
      (fun k => fderiv ℝ (fun y => (Dseq k).curvatureTensor y a b c d) (pseq k) u)
      atTop (𝓝 (fderiv ℝ (fun y => D.curvatureTensor y a b c d) p u)) := by
    let C := continuousMultilinearCurryFin1 ℝ V ℝ
    have heq (f : V → ℝ) (x : V) : C (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
      ext v
      simp [C, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    have h := (C.continuous.tendsto _).comp
      (curvatureTensor_jets_tendsto_of_metric_jets Dseq D pseq p a b c d 1 hjet)
    have h' : Tendsto
        (fun k => fderiv ℝ (fun y => (Dseq k).curvatureTensor y a b c d) (pseq k))
        atTop (𝓝 (fderiv ℝ (fun y => D.curvatureTensor y a b c d) p)) := by
      simpa only [Function.comp_def, heq] using h
    exact ((ContinuousLinearMap.apply ℝ ℝ u).continuous.tendsto _).comp h'
  let A (g' : RiemannianMetric 3 V) (D' : LeviCivitaData g') (x : V) : V →ₗ[ℝ] ℝ :=
    { toFun := fun v => D'.curvatureTensor x v b c d
      map_add' := fun v w => D'.curvatureTensor_add_first x v w b c d
      map_smul' := fun q v => D'.curvatureTensor_smul_first x q v b c d }
  let B (g' : RiemannianMetric 3 V) (D' : LeviCivitaData g') (x : V) : V →ₗ[ℝ] ℝ :=
    { toFun := fun v => D'.curvatureTensor x a v c d
      map_add' := fun v w => D'.curvatureTensor_add_second x a v w c d
      map_smul' := fun q v => D'.curvatureTensor_smul_second x q a v c d }
  let C (g' : RiemannianMetric 3 V) (D' : LeviCivitaData g') (x : V) : V →ₗ[ℝ] ℝ :=
    { toFun := fun v => D'.curvatureTensor x a b v d
      map_add' := fun v w => D'.curvatureTensor_add_third x a b v d w
      map_smul' := fun q v => D'.curvatureTensor_smul_third x q a b v d }
  let F (g' : RiemannianMetric 3 V) (D' : LeviCivitaData g') (x : V) : V →ₗ[ℝ] ℝ :=
    { toFun := fun v => D'.curvatureTensor x a b c v
      map_add' := fun v w => D'.curvatureTensor_add_last x a b c v w
      map_smul' := fun q v => D'.curvatureTensor_smul_last x q a b c v }
  have hA := linear_eval_tendsto (fun k => A (gseq k) (Dseq k) (pseq k)) (A g D p)
    (hconn u a) (fun i => hcurv (EuclideanSpace.basisFun (Fin 3) ℝ i) b c d)
  have hB := linear_eval_tendsto (fun k => B (gseq k) (Dseq k) (pseq k)) (B g D p)
    (hconn u b) (fun i => hcurv a (EuclideanSpace.basisFun (Fin 3) ℝ i) c d)
  have hC := linear_eval_tendsto (fun k => C (gseq k) (Dseq k) (pseq k)) (C g D p)
    (hconn u c) (fun i => hcurv a b (EuclideanSpace.basisFun (Fin 3) ℝ i) d)
  have hF := linear_eval_tendsto (fun k => F (gseq k) (Dseq k) (pseq k)) (F g D p)
    (hconn u d) (fun i => hcurv a b c (EuclideanSpace.basisFun (Fin 3) ℝ i))
  simp_rw [curvature_derivative_const]
  exact hderiv.sub (((hA.add hB).add hC).add hF)

end PoincareConjecture.M35
