import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.ModelNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.SphereCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Model.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Diffeomorph.Sphere

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M27SphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem exists_scalarNormalized_sphere (C : M27SphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (p : M) :
    0 < (K.flow.connection t).scalarCurvature p ∧
      ∃ a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere,
        ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
          (K.flow.connection t).scalarCurvature p * (C.sphere.metric t).inner (a x)
            (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
              2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w := by
  have heq : (K.flow.connection t).scalarCurvature p =
      (C.sphere.connection t).scalarCurvature (C.identification.symm p).1 := by
    simpa only [C.identification.apply_symm_apply] using
      (C.sphere.metric t).scalarCurvature_eq_of_line_product (K.flow.metric t)
        (C.sphere.connection t) (K.flow.connection t) C.identification
        (C.metric_transport t ht) (C.identification.symm p)
  obtain ⟨hpos, q, _, _, hlocal, hmetric, _⟩ :=
    exists_scalarNormalized_roundSurface_cover (C.sphere.metric t)
      (C.sphere.connection t) (C.sphere.round t ht) (C.identification.symm p).1
  let a := Poincare.Geometry.Manifold.sphereDiffeomorphOfLocalDiffeomorph q hlocal
  refine ⟨heq.symm ▸ hpos, a, ?_⟩
  intro x v w
  rw [heq]
  exact hmetric x v w

end PoincareConjecture.M27SphereLineFlowCertificate
