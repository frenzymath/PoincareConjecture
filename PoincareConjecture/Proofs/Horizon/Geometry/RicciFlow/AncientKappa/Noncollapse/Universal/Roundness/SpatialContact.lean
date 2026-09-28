import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TensorCone
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.CarrierContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open PoincareConjecture.AncientKappaRoundness
open scoped Manifold ContDiff Bundle InnerProductSpace

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

theorem tensorLaplacian_nonpos_at_round_pinching_contact
    (D : LeviCivitaData g) (p : M) (c : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (T : (x : M) → TensorFiber (TangentSpace (𝓡 3) x) 2)
      (hT : IsSmoothCovariantTensor (fun x v => T x v))
      (q : TensorFiber (TangentSpace (𝓡 3) p) 2 ×
        TensorFiber (TangentSpace (𝓡 3) p) 2),
      q ∈ Poincare.Parabolic.unitSupportSet (tensorPinchingCone c) →
      ⟪q.2, T p - q.1⟫_ℝ = Metric.infDist (T p) (tensorPinchingCone c) →
      IsLocalMax (fun x => Metric.infDist (T x) (tensorPinchingCone c)) p →
      ⟪q.2, D.tensorLaplacianFiber hT p⟫_ℝ ≤ 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro T hT q hq hactive hmax
  obtain ⟨r, Y, hr, hrU, hY, hinit, hpar, P, hP, hcontact⟩ :=
    D.exists_radialCarrierContact p
  exact hcontact 2 T (fun _ => tensorPinchingCone c)
    hT (tensorPinchingCone_nonempty c) (isClosed_tensorPinchingCone c)
    (convex_tensorPinchingCone c)
    (fun x => tensorPinchingCone_transport_image (P x) c) q hq hactive hmax

end PoincareConjecture.LeviCivitaData
