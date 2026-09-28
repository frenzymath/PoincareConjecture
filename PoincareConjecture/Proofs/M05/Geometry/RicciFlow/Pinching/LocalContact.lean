
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.TensorRegion
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.CarrierContact












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle InnerProductSpace
open Poincare.HamiltonIvey

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

omit [T2Space M] in
private theorem finrank_tangent (x : M) : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
  rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
  simp



theorem tensorLaplacian_nonpos_at_pinching_contact
    (D : LeviCivitaData g) (p : M) {t : ℝ} (ht : 0 ≤ t) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (T : (x : M) → TensorFiber (TangentSpace (𝓡 3) x) 2)
      (hT : IsSmoothCovariantTensor (fun x v => T x v))
      (q : TensorFiber (TangentSpace (𝓡 3) p) 2 ×
        TensorFiber (TangentSpace (𝓡 3) p) 2),
      q ∈ Poincare.Parabolic.unitSupportSet (tensorRegion (finrank_tangent p) t) →
      ⟪q.2, T p - q.1⟫_ℝ = Metric.infDist (T p) (tensorRegion (finrank_tangent p) t) →
      IsLocalMax (fun x => Metric.infDist (T x) (tensorRegion (finrank_tangent x) t)) p →
      ⟪q.2, D.tensorLaplacianFiber hT p⟫_ℝ ≤ 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro T hT q hq hactive hmax
  obtain ⟨r, Y, hr, hrU, hY, hinit, hpar, P, hP, hcontact⟩ :=
    D.exists_radialCarrierContact p
  exact hcontact 2 T (fun x => tensorRegion (finrank_tangent x) t)
    hT (tensorRegion_nonempty _ ht) (isClosed_tensorRegion _ ht)
    (convex_tensorRegion _ ht)
    (fun x => tensorRegion_transport_image _ _ (P x) ht) q hq hactive hmax

end PoincareConjecture.LeviCivitaData
