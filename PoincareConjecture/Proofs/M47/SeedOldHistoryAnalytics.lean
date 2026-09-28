import PoincareConjecture.Proofs.M47.JointSeedBallScalar
import PoincareConjecture.Proofs.M47.PositiveHistoryAnalytics
import PoincareConjecture.Proofs.M47.SeedTube
import PoincareConjecture.Proofs.M47.ComponentEstimateCylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_old_history_analytic_bound
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p) :
    ∃ A : ℝ, 1 ≤ A ∧ S.setup.C ≤ A ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryPrefixControls p F O →
        ∀ (C : GeneralizedSliceCarrier.{u}) (origin scale : ℝ) (I J : Set ℝ)
          (U : TopologicalSpace.Opens C.carrier),
          IsCompact (U : Set C.carrier) → IsConnected (U : Set C.carrier) →
          ∀ (e : SurgeryFlowCylinder F C origin scale I U) (s : ℝ) (hs : s ∈ I),
            origin + s / scale ∈ surgeryObservationInterval O ∩ prefixFinalInterval p →
            ∀ (G : RicciFlow 3 U J) (t L : ℝ),
              origin + s / scale ≤ t → Icc (origin + s / scale) t ⊆ J →
              (∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
                (F.metric (origin + s / scale)).inner (e.forward s hs y.val)
                  (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
                  (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w) =
                    (G.metric (origin + s / scale)).inner y v w) →
              (∀ y : U, (G.connection (origin + s / scale)).scalarCurvature y =
                (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs y.val)) →
              (∀ y : U, 0 ≤ (G.connection (origin + s / scale)).scalarCurvature y) →
              ∀ q z : U, S.setup.C * (G.connection t).scalarCurvature q ≤ L →
                (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ L →
                L < (G.connection (origin + s / scale)).scalarCurvature z →
                M45PointwiseAnalyticEstimate (G.metric (origin + s / scale))
                  (G.connection (origin + s / scale)) z A := by
  obtain ⟨A, hA, hCA, hmodel⟩ := M47.exists_jointSeed_physical_analytic_bound.{u} S.setup.C
  let PS : M47ScalarPersistencePredecessors.{u} := {
    tensor_calculus := fun M _ _ _ => P.m04.tensor_calculus 3 M
    scalar_regular := fun M _ _ _ => P.m04.scalar_regular 3 M
    scalar_evolution := fun M _ _ _ => P.m04.scalar_evolution 3 M }
  refine ⟨A, hA, hCA, ?_⟩
  intro F O old C origin scale I J U hcompact hconnected e s hs htime G t L hst hJ
    hmetric hread hnonnegative q z hterminal hlevel hhigh
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  have himage := M47.component_cylinder_image_eq e U.isOpen hcompact hconnected s hs z.property
  have hcomponent (y : U) : e.forward s hs y.val ∈ connectedComponent (e.forward s hs z.val) := by
    rw [← himage]
    exact mem_image_of_mem _ y.property
  obtain ⟨y, hy, hgap⟩ := M47.jointSeed_physical_reference_low_point_gap PS G F q z
    (fun y : U => e.forward s hs y.val) hcomponent hread hst hJ S.setup.C_large
    hnonnegative hterminal hhigh
  have hscalar : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs z.val) := by
    rw [← hread]
    exact hlevel.trans hhigh.le
  have hcanonical := old_prefix_seed_canonical S p compatible old htime (e.forward s hs z.val)
    hscalar
  have hanalytic := hmodel F _ y (e.forward s hs z.val) hy hgap hcanonical
  exact M47Positive.cylinder_pointwise_analytic_estimate U e s hs
    (G.metric (origin + s / scale)) (G.connection (origin + s / scale))
    (P.m04.tensor_calculus 3 _ (F.metric (origin + s / scale))
      (F.connection (origin + s / scale))) hmetric hanalytic

end PoincareConjecture.Proofs.M47
