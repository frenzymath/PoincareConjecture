
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.LocalContact
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.TensorConnection











noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology InnerProductSpace
open Poincare.HamiltonIvey

universe u

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private instance tangentFiniteDimensional_transportContact (x : M) :
    FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

omit [T2Space M] in
private theorem finrank_tangent_contact (x : M) :
    Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
  simp



theorem tensorLaplacian_pullback_nonpos_at_pinching_contact
    {E : M → Type*} [∀ x, NormedAddCommGroup (E x)]
    [∀ x, InnerProductSpace ℝ (E x)] [∀ x, FiniteDimensional ℝ (E x)]
    (hn : ∀ x, Module.finrank ℝ (E x) = 3)
    (D : LeviCivitaData g)
    (e : ∀ x, E x ≃ₗ[ℝ] TangentSpace (𝓡 3) x)
    (he : ∀ x v w, g.inner x (e x v) (e x w) = inner ℝ v w)
    (T : (x : M) → TensorFiber (TangentSpace (𝓡 3) x) 2)
    (hT : IsSmoothCovariantTensor (fun x v => T x v))
    (p : M) {s : ℝ} (hs : 0 ≤ s)
    (q : TensorFiber (E p) 2 × TensorFiber (E p) 2)
    (hq : q ∈ Poincare.Parabolic.unitSupportSet (tensorRegion (hn p) s))
    (hactive : ⟪q.2, TensorFiber.toMultilinear.symm
        ((TensorFiber.toMultilinear (T p)).compLinearMap (fun _ => (e p).toLinearMap)) -
          q.1⟫_ℝ = Metric.infDist
        (TensorFiber.toMultilinear.symm
          ((TensorFiber.toMultilinear (T p)).compLinearMap (fun _ => (e p).toLinearMap)))
        (tensorRegion (hn p) s))
    (hmax : IsLocalMax (fun x => Metric.infDist
        (TensorFiber.toMultilinear.symm
          ((TensorFiber.toMultilinear (T x)).compLinearMap (fun _ => (e x).toLinearMap)))
        (tensorRegion (hn x) s)) p) :
    ⟪q.2, TensorFiber.toMultilinear.symm
      ((TensorFiber.toMultilinear (D.tensorLaplacianFiber hT p)).compLinearMap
        (fun _ => (e p).toLinearMap))⟫_ℝ ≤ 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let L (x : M) : E x ≃ₗᵢ[ℝ] TangentSpace (𝓡 3) x := (e x).isometryOfInner (he x)
  let P (x : M) := TensorFiber.transport (L x) 2
  have hpull (x : M) : (P x).symm (T x) =
      TensorFiber.toMultilinear.symm
        ((TensorFiber.toMultilinear (T x)).compLinearMap (fun _ => (e x).toLinearMap)) := by
    apply TensorFiber.ext
    intro v
    change T x (fun i => L x (v i)) = T x (fun i => e x (v i))
    congr 1
  have hmap (x : M) : P x '' tensorRegion (hn x) s =
      tensorRegion (finrank_tangent_contact x) s :=
    tensorRegion_transport_image (hn x) (finrank_tangent_contact x) (L x) hs
  have hdist (x : M) : Metric.infDist (T x) (tensorRegion (finrank_tangent_contact x) s) =
      Metric.infDist ((P x).symm (T x)) (tensorRegion (hn x) s) :=
    Poincare.Parabolic.infDist_pullback_carrier (P x) (hmap x) (T x)
  have hq' := Poincare.Parabolic.unitSupport_map (P p) hq
  rw [hmap] at hq'
  have hactive' : ⟪P p q.2, T p - P p q.1⟫_ℝ =
      Metric.infDist (T p) (tensorRegion (finrank_tangent_contact p) s) := by
    rw [Poincare.Parabolic.support_eval_pullback, hdist]
    exact hactive
  have hmax' : IsLocalMax
      (fun x => Metric.infDist (T x) (tensorRegion (finrank_tangent_contact x) s)) p := by
    rw [show (fun x => Metric.infDist
        (TensorFiber.toMultilinear.symm
          ((TensorFiber.toMultilinear (T x)).compLinearMap (fun _ => (e x).toLinearMap)))
        (tensorRegion (hn x) s)) =
      (fun x => Metric.infDist ((P x).symm (T x)) (tensorRegion (hn x) s)) by
        funext x; rw [hpull]] at hmax
    simpa only [hdist] using hmax
  have h := D.tensorLaplacian_nonpos_at_pinching_contact p hs T hT
    (P p q.1, P p q.2) hq' hactive' hmax'
  have hinner := (P p).inner_map_map q.2 ((P p).symm (D.tensorLaplacianFiber hT p))
  rw [(P p).apply_symm_apply] at hinner
  rw [hinner] at h
  exact h

end PoincareConjecture.LeviCivitaData
