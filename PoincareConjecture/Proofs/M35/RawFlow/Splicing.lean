import PoincareConjecture.Definitions.Ch12.StandardCap
import PoincareConjecture.Proofs.Ch01.CurvatureConnection

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.PartialStandardCapFlow

noncomputable def extensionOfMetricAgreement
    {g₀ : StandardInitialMetric} (F G : PartialStandardCapFlow g₀)
    (hlt : F.lifetime < G.lifetime)
    (hmetric : Set.EqOn F.flow.metric G.flow.metric (Set.Ico 0 F.lifetime)) :
    PartialStandardCapFlowExtension F G.lifetime := by
  classical
  let D (t : ℝ) : LeviCivitaData (G.flow.metric t) :=
    if ht : t ∈ Set.Ico 0 F.lifetime then
      cast (congrArg (fun g : RiemannianMetric 3 StandardCapSpace => LeviCivitaData g)
        (hmetric ht)) (F.flow.connection t)
    else G.flow.connection t
  have hD (t : ℝ) (ht : t ∈ Set.Ico 0 F.lifetime) :
      HEq (D t) (F.flow.connection t) := by
    dsimp only [D]
    rw [dif_pos ht]
    exact cast_heq _ _
  refine {
    lifetime_gt := hlt
    flow := { G.flow with
      connection := D
      equation := ?_ }
    initial_metric := G.initial_metric
    initial_connection := (hD 0 ⟨le_rfl, F.lifetime_pos⟩).trans F.initial_connection
    agrees_on_old_domain := fun t ht => (hmetric ht).symm
    agrees_on_connection := hD
    curvature_locally_bounded := ?_
  }
  · intro t ht x u v
    rw [(D t).ricci_eq (G.flow.connection t)]
    exact G.flow.equation t ht x u v
  · intro T hT hTlt
    obtain ⟨K, hK, hbound⟩ := G.curvature_locally_bounded T hT hTlt
    refine ⟨K, hK, ?_⟩
    intro t ht x
    change |(D t).curvatureTensorNorm x| ≤ K
    rw [(D t).curvatureTensorNorm_eq (G.flow.connection t)]
    exact hbound t ht x

end PoincareConjecture.PartialStandardCapFlow
