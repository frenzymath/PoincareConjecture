import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Connection
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Normal
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Spectral

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
open PoincareConjecture
open scoped ContDiff InnerProductSpace Topology

namespace Poincare.Geometry.Curvature.Hypersurface

variable {m n : ℕ}
  {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
  {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))}

def secondFundamentalFormBilinear (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) where
  toFun u := {
    toFun := secondFundamentalForm D D' F x u
    map_add' := by
      intro v w
      simp only [secondFundamentalForm, covariantHessianMap, map_add]
      abel
    map_smul' := by
      intro c v
      simp only [secondFundamentalForm, covariantHessianMap, map_smul, smul_add, smul_sub]
      rfl }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change secondFundamentalForm D D' F x (u + v) w =
      secondFundamentalForm D D' F x u w + secondFundamentalForm D D' F x v w
    simp only [secondFundamentalForm, covariantHessianMap, map_add, add_apply]
    abel
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    change secondFundamentalForm D D' F x (c • u) v =
      c • secondFundamentalForm D D' F x u v
    simp only [secondFundamentalForm, covariantHessianMap, map_smul, smul_apply,
      smul_add, smul_sub]

def scalarSecondFundamentalForm (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin m)) (N : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ :=
  (secondFundamentalFormBilinear D D' F x).compr₂ (g.inner (F x) N).toLinearMap

def shapeOperator (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin m)) (N : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  (show EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ
    from h.inner x).inverse.toLinearMap.comp
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (scalarSecondFundamentalForm D D' F x N))

theorem inner_shapeOperator (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (x u v : EuclideanSpace ℝ (Fin m)) (N : EuclideanSpace ℝ (Fin n)) :
    h.inner x (shapeOperator D D' F x N u) v =
      g.inner (F x) N (secondFundamentalForm D D' F x u v) := by
  have he := congrArg (fun L => L v) ((h.inner_isInvertible x).self_apply_inverse
    (show EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ from
      LinearMap.toContinuousLinearMap (scalarSecondFundamentalForm D D' F x N u)))
  exact he

theorem shapeOperator_selfAdjoint (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} (hF : ContDiffAt ℝ ∞ F x)
    (N : EuclideanSpace ℝ (Fin n)) (u v : EuclideanSpace ℝ (Fin m)) :
    h.inner x (shapeOperator D D' F x N u) v =
      h.inner x u (shapeOperator D D' F x N v) := by
  rw [h.symm x u, inner_shapeOperator, inner_shapeOperator,
    secondFundamentalForm_symm D D' hF]

theorem inner_shapeOperator_neg_normal_eq_normal_derivative
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} (hF : ContDiffAt ℝ ∞ F x)
    {N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hN : DifferentiableAt ℝ N x)
    (hNT : ∀ᶠ y in 𝓝 x, ∀ v,
      g.inner (F y) (N y) (fderiv ℝ F y v) = 0)
    (u v : EuclideanSpace ℝ (Fin m)) :
    h.inner x (shapeOperator D D' F x (-N x) u) v =
      g.inner (F x) (covariantDerivativeAlongMap D F N x u) (fderiv ℝ F x v) := by
  have hzero : (fun y => g.inner (F y) (N y) (fderiv ℝ F y v))
      =ᶠ[𝓝 x] fun _ => 0 := hNT.mono fun _ hy => hy v
  have hc : ContDiffAt ℝ ∞ (fun y => fderiv ℝ F y v) x :=
    (hF.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hd := hc.differentiableAt (by simp)
  have hp := covariantDerivativeAlongMap_metricCompatible D
    (hF.differentiableAt (by simp)) hN hd u
  rw [hzero.fderiv_eq, fderiv_const_apply, zero_apply,
    covariantDerivativeAlongMap_fderiv_const D hF] at hp
  have hn := hNT.self_of_nhds (D'.connectionCoefficient x u v)
  rw [inner_shapeOperator]
  simp only [map_neg, neg_apply, secondFundamentalForm, map_sub, hn, sub_zero]
  linarith

end Poincare.Geometry.Curvature.Hypersurface
