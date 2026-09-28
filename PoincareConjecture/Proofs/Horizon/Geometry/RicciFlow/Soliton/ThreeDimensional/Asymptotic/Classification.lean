import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Transport.SmallCarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Certificate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.SelfSimilarity.LiftedFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Classification.Static

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  uliftSecondCountable uliftConnected

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem classificationCertificate_of_bounded_curvature
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B) :
    ThreeDimensionalAsymptoticClassificationCertificate S L := by
  letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  let G := L.shrinkingSolitonFlow hP.curvature hbound
  let H := L.liftedShrinkingSolitonFlow hP.curvature hbound
  let d : (ULift.{u} L.convergence.limit.carrier.carrier) ≃ₘ⟮𝓡 3, 𝓡 3⟯
      L.convergence.limit.carrier.carrier :=
    Poincare.Manifold.uliftDiffeomorph (𝓡 3) L.convergence.limit.carrier.carrier
  have hmetric (t : ℝ) (_ht : t < 0)
      (x : L.convergence.limit.carrier.carrier) (v w : TangentSpace (𝓡 3) x) :
      (G.flow.metric t).inner x v w =
        (H.flow.metric t).inner (d.symm x)
          (mfderiv (𝓡 3) (𝓡 3) d.symm x v)
          (mfderiv (𝓡 3) (𝓡 3) d.symm x w) := by
    have hd (v : TangentSpace (𝓡 3) x) :
        mfderiv (𝓡 3) (𝓡 3) d (d.symm x)
          (mfderiv (𝓡 3) (𝓡 3) d.symm x v) = v := by
      have h := mfderiv_comp x (d.contMDiff.mdifferentiable (by simp) _)
        (d.symm.contMDiff.mdifferentiable (by simp) x)
      have hcomp : d ∘ d.symm = id := funext d.apply_symm_apply
      rw [hcomp, mfderiv_id] at h
      exact congrArg (fun A => A v) h.symm
    change (L.convergence.limit.flow.metric t).inner x v w =
      (L.convergence.limit.flow.metric t).inner (d (d.symm x))
        (mfderiv (𝓡 3) (𝓡 3) d (d.symm x)
          (mfderiv (𝓡 3) (𝓡 3) d.symm x v))
        (mfderiv (𝓡 3) (𝓡 3) d (d.symm x)
          (mfderiv (𝓡 3) (𝓡 3) d.symm x w))
    rw [hd v, hd w, d.apply_symm_apply]
  obtain ⟨model⟩ := H.threeDimensionalSolitonModel hP
  refine ⟨hbound, ?_⟩
  exact ⟨_, G, rfl, rfl, ⟨model.toSmallCarrier G H d.symm hmetric⟩⟩

end PoincareConjecture.AncientAsymptoticSolitonLimitData
