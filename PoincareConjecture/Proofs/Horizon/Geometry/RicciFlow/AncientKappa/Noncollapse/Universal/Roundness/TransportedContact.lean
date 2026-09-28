import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.SpatialContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.RicciComplementEvolution











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle
open PoincareConjecture.AncientKappaRoundness PoincareConjecture.RicciFlow.Frame
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance



theorem tensorLaplacian_pullback_nonpos_at_round_pinching_contact
    {E : M → Type*} [∀ x, NormedAddCommGroup (E x)]
    [∀ x, InnerProductSpace ℝ (E x)] [∀ x, FiniteDimensional ℝ (E x)]
    (D : LeviCivitaData g)
    (e : ∀ x, E x ≃ₗ[ℝ] TangentSpace (𝓡 3) x)
    (he : ∀ x v w, g.inner x (e x v) (e x w) = inner ℝ v w)
    (T : (x : M) → TensorFiber (TangentSpace (𝓡 3) x) 2)
    (hT : IsSmoothCovariantTensor (fun x v => T x v))
    (p : M) (c : ℝ)
    (q : TensorFiber (E p) 2 × TensorFiber (E p) 2)
    (hq : q ∈ Poincare.Parabolic.unitSupportSet (tensorPinchingCone c))
    (hactive : ⟪q.2, TensorFiber.toMultilinear.symm
        ((TensorFiber.toMultilinear (T p)).compLinearMap (fun _ => (e p).toLinearMap)) -
          q.1⟫_ℝ = Metric.infDist
        (TensorFiber.toMultilinear.symm
          ((TensorFiber.toMultilinear (T p)).compLinearMap (fun _ => (e p).toLinearMap)))
        (tensorPinchingCone c))
    (hmax : IsLocalMax (fun x => Metric.infDist
        (TensorFiber.toMultilinear.symm
          ((TensorFiber.toMultilinear (T x)).compLinearMap (fun _ => (e x).toLinearMap)))
        (tensorPinchingCone c)) p) :
    ⟪q.2, TensorFiber.toMultilinear.symm
      ((TensorFiber.toMultilinear (D.tensorLaplacianFiber hT p)).compLinearMap
        (fun _ => (e p).toLinearMap))⟫_ℝ ≤ 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
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
  have hmap (x : M) : P x '' tensorPinchingCone c = tensorPinchingCone c :=
    tensorPinchingCone_transport_image (L x) c
  have hdist (x : M) : Metric.infDist (T x) (tensorPinchingCone c) =
      Metric.infDist ((P x).symm (T x)) (tensorPinchingCone c) :=
    Poincare.Parabolic.infDist_pullback_carrier (P x) (hmap x) (T x)
  have hq' := Poincare.Parabolic.unitSupport_map (P p) hq
  rw [hmap] at hq'
  have hactive' : ⟪P p q.2, T p - P p q.1⟫_ℝ =
      Metric.infDist (T p) (tensorPinchingCone c) := by
    rw [Poincare.Parabolic.support_eval_pullback, hdist]
    exact hactive
  have hmax' : IsLocalMax (fun x => Metric.infDist (T x) (tensorPinchingCone c)) p := by
    simpa only [hdist, hpull] using hmax
  have h := D.tensorLaplacian_nonpos_at_round_pinching_contact p c T hT
    (P p q.1, P p q.2) hq' hactive' hmax'
  have hinner := (P p).inner_map_map q.2 ((P p).symm (D.tensorLaplacianFiber hT p))
  rw [(P p).apply_symm_apply] at hinner
  rw [hinner] at h
  exact h

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.AncientKappaRoundness

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance



theorem transportedRicciComplementDiffusion_nonpos_at_contact
    (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus)
    (hab : a < b) {t : ℝ} (ht : t ∈ Ico a b) (p : M) (c : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    ∀ q : TensorFiber (TangentSpace (𝓡 3) p) 2 × TensorFiber (TangentSpace (𝓡 3) p) 2,
      q ∈ Poincare.Parabolic.unitSupportSet (tensorPinchingCone c) →
      ⟪q.2, transportedRicciComplement F hcalculus t p - q.1⟫_ℝ =
        Metric.infDist (transportedRicciComplement F hcalculus t p) (tensorPinchingCone c) →
      IsLocalMax (fun x => Metric.infDist
        (transportedRicciComplement F hcalculus t x) (tensorPinchingCone c)) p →
      ⟪q.2, transportedRicciComplementDiffusion F hcalculus t p⟫_ℝ ≤ 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  intro q hq hactive hmax
  let D := F.connection t
  let T (x : M) := D.ricciComplementTensor (hcalculus t) x
  have hT : IsSmoothCovariantTensor (fun x v => T x v) := by
    simpa only [T, LeviCivitaData.ricciComplementTensor_apply] using
      D.isSmoothCovariantTensor_ricciComplementEvaluation (hcalculus t)
  let e (x : M) := (orthonormalTransport F t x).toLinearEquiv
  have hpull (x : M) : TensorFiber.toMultilinear.symm
      ((TensorFiber.toMultilinear (T x)).compLinearMap (fun _ => (e x).toLinearMap)) =
      transportedRicciComplement F hcalculus t x := by
    apply TensorFiber.ext
    intro v
    rfl
  have hlap : TensorFiber.toMultilinear.symm
      ((TensorFiber.toMultilinear (D.tensorLaplacianFiber hT p)).compLinearMap
        (fun _ => (e p).toLinearMap)) =
      transportedRicciComplementDiffusion F hcalculus t p := by
    apply TensorFiber.ext
    intro v
    simp only [LinearEquiv.apply_symm_apply, MultilinearMap.compLinearMap_apply,
      LeviCivitaData.tensorLaplacianFiber_apply, transportedRicciComplementDiffusion_apply,
      T, LeviCivitaData.ricciComplementTensor_apply]
    rw [← orthonormalTransport_toContinuousLinearMap F t p]
    rfl
  have h := D.tensorLaplacian_pullback_nonpos_at_round_pinching_contact e
    (canonicalTransport_pairing F hab ht) T hT p c q hq
    (by simpa only [hpull] using hactive) (by simpa only [hpull] using hmax)
  rwa [hlap] at h

end PoincareConjecture.AncientKappaRoundness
