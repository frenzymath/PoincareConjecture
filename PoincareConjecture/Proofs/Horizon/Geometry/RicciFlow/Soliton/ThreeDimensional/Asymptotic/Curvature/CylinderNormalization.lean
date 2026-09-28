import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.AntipodalExclusion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold

variable {S : ℕ → FlowCarrier.{0} 3} {g : ∀ k, ℝ → (S k).metric}
  {p : ∀ k, (S k).carrier} {T : ℝ}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
  [T2Space C] [T3Space C] [ConnectedSpace C] [CompactSpace C]

theorem exists_centered_scalarNormalized_roundCylinder_of_ulift_round_surface_product
    (G : AncientPointedGeometricConvergence S g p T)
    (hE : ∀ᶠ i in atTop, Nonempty
      ((S (G.subsequence i)).carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3)))
    (gC : RiemannianMetric 2 C) (D : LeviCivitaData gC)
    (hround : ConstantPositiveSectionalCurvature gC D)
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ ULift.{u} G.limitCarrier.carrier)
    (hmetric : ∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (G.limitFlow.ulift.metric 0).inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          gC.inner z.1 v.1 w.1 + v.2 * w.2) :
    0 < (G.limitFlow.connection 0).scalarCurvature G.base ∧
      ∃ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
        (q : UnitTwoSphere), Φ (q, 0) = G.base ∧
        (fun z v w => (G.limitFlow.connection 0).scalarCurvature G.base *
          roundCylinderPullback (G.limitFlow.metric 0) Φ z v w) = EvolvingRoundCylinderMetric 0 := by
  let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) G.limitCarrier.carrier
  let e₀ := e.trans d
  apply G.exists_centered_scalarNormalized_roundCylinder_of_round_surface_product
    hE gC D hround e₀
  intro z v w
  have hd : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e₀ z =
      (mfderiv (𝓡 3) (𝓡 3) d (e z)).comp
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z) :=
    mfderiv_comp z (d.contMDiff.mdifferentiable (by simp) (e z))
      (e.contMDiff.mdifferentiable (by simp) z)
  rw [hd]
  exact hmetric z v w

end PoincareConjecture.AncientPointedGeometricConvergence
