import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.TimeEvolution
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.TransportedContact
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Laplacian.Linearity

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology InnerProductSpace
open Poincare.HamiltonIvey

universe u

namespace PoincareConjecture.RicciFlow.Frame

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

theorem scaled_transportedRicciComplementLaplacian_nonpos_at_contact
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (hab : a < b) {t : ℝ} (ht : t ∈ Ico a b)
    (hn : ∀ x : M, Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    ∀ q ∈ Poincare.Parabolic.unitSupportSet (tensorRegion (hn p) 0),
      ⟪q.2, (1 + t) • transportedRicciComplementTensor F hC t p - q.1⟫_ℝ =
        Metric.infDist ((1 + t) • transportedRicciComplementTensor F hC t p)
          (tensorRegion (hn p) 0) →
      IsLocalMax (fun x => Metric.infDist
        ((1 + t) • transportedRicciComplementTensor F hC t x)
        (tensorRegion (hn x) 0)) p →
      ⟪q.2, (1 + t) • transportedRicciComplementLaplacian F hC t p⟫_ℝ ≤ 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  intro q hq hactive hmax
  let D := F.connection t
  let T (x : M) := (1 + t) • D.ricciComplementTensor
    (hC.tensor_calculus 3 M (F.metric t) D) x
  have hR := D.isSmoothCovariantTensor_ricciComplementEvaluation
    (hC.tensor_calculus 3 M (F.metric t) D)
  have hT : IsSmoothCovariantTensor (fun x v => T x v) := by
    simpa only [T, TensorFiber.smul_apply, smul_eq_mul,
      LeviCivitaData.ricciComplementTensor_apply] using hR.const_mul (1 + t)
  let e (x : M) := (orthonormalTransport F t x).toLinearEquiv
  have hpull (x : M) : TensorFiber.toMultilinear.symm
      ((TensorFiber.toMultilinear (T x)).compLinearMap (fun _ => (e x).toLinearMap)) =
      (1 + t) • transportedRicciComplementTensor F hC t x := by
    apply TensorFiber.ext
    intro v
    rfl
  have hlap : TensorFiber.toMultilinear.symm
      ((TensorFiber.toMultilinear (D.tensorLaplacianFiber hT p)).compLinearMap
        (fun _ => (e p).toLinearMap)) =
      (1 + t) • transportedRicciComplementLaplacian F hC t p := by
    apply TensorFiber.ext
    intro v
    simp only [LinearEquiv.apply_symm_apply, MultilinearMap.compLinearMap_apply,
      LeviCivitaData.tensorLaplacianFiber_apply, TensorFiber.smul_apply,
      smul_eq_mul, transportedRicciComplementLaplacian_apply]
    simp only [T, TensorFiber.smul_apply, smul_eq_mul,
      LeviCivitaData.ricciComplementTensor_apply]
    rw [D.tensorLaplacian_const_mul hR (D.covariantTensorDerivative_isSmooth hR)]
    rw [← orthonormalTransport_toContinuousLinearMap F t p]
    rfl
  have h := D.tensorLaplacian_pullback_nonpos_at_pinching_contact hn e
    (canonicalTransport_pairing F hab ht) T hT p (s := 0) (by norm_num) q hq
    (by simpa only [hpull] using hactive) (by simpa only [hpull] using hmax)
  rwa [hlap] at h

end PoincareConjecture.RicciFlow.Frame
