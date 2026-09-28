import PoincareConjecture.Proofs.M47.LimitCanonicalCompressedFamily
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckMetricTransport
import PoincareConjecture.Definitions.M30ControlledBlowupLimits










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤))

private local instance : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier :=
  L.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
private local instance : MeasurableSpace L.carrier.carrier := L.carrier.measurableSpace
private local instance : BorelSpace L.carrier.carrier := L.carrier.borelSpace
private local instance : T2Space L.carrier.carrier := L.carrier.t2Space
private local instance : T3Space L.carrier.carrier := L.carrier.t3Space
private local instance : SecondCountableTopology L.carrier.carrier := L.carrier.secondCountable
private local instance : ConnectedSpace L.carrier.carrier := L.connectedSpace



theorem limitCanonical_exists_ancient_neck_family
    {kappa epsilon : ℝ} (A : M30AncientKappaIdentification L kappa)
    (N : StrongEvolvingNeck A.certificate.solution 0 epsilon)
    (hcenter : N.center = L.base) :
    ∃ N' : EpsilonNeck (L.flow.metric 0),
      N'.epsilon = epsilon ∧ N'.center = L.base ∧
      N'.connection = L.flow.connection 0 ∧ N'.scale = 1 ∧
      ∃ K : Set L.sliceCarrier.carrier, IsCompact K ∧ N'.carrier ⊆ K ∧
        RoundCylinderFamilyClose N'.epsilon (Ioc (-1 : ℝ) 0)
          (fun s => roundCylinderPullback (L.flow.metric s) N'.coordinate_map) := by
  let S := A.certificate.solution
  have hpair : (⟨S.flow.metric 0, S.flow.connection 0⟩ :
      Σ g : RiemannianMetric 3 L.carrier.carrier, LeviCivitaData g) =
      ⟨L.flow.metric 0, L.flow.connection 0⟩ :=
    Sigma.ext (A.certificate.metric_eq 0 le_rfl) (A.connection_eq 0 le_rfl)
  have hscalar := congrArg (fun gd :
      Σ g : RiemannianMetric 3 L.carrier.carrier, LeviCivitaData g =>
      gd.2.scalarCurvature L.base) hpair
  change (S.flow.connection 0).scalarCurvature L.base =
    (L.flow.connection 0).scalarCurvature L.base at hscalar
  rw [L.scalar_normalized] at hscalar
  have hnscalar : (S.flow.connection 0).scalarCurvature N.center = 1 := by
    rw [hcenter]
    exact hscalar
  let N0 := N.terminal_neck.ofMetricEq (A.certificate.metric_eq 0 le_rfl)
  obtain ⟨hepsilon, hNcenter, hcoordinate⟩ :=
    N.terminal_neck.ofMetricEq_data (A.certificate.metric_eq 0 le_rfl)
  have hfamily : RoundCylinderFamilyClose N0.epsilon (Ioc (-1 : ℝ) 0)
      (fun s => roundCylinderPullback (L.flow.metric s) N0.coordinate_map) := by
    rw [hepsilon, N.terminal_epsilon]
    apply N.metric_comparison.congr_cylinder
    intro s hs z _ v w
    rw [hnscalar, div_one, zero_add, one_mul, A.certificate.metric_eq s hs.2, hcoordinate]
  obtain ⟨N', hNe, hNc, hND, hNs, K, hK, hNK, hNfamily⟩ :=
    limitCanonical_exists_compressed_limit_family L N0
      (hNcenter.trans (N.terminal_center.trans hcenter)) hfamily
  exact ⟨N', hNe.trans (hepsilon.trans N.terminal_epsilon),
    hNc, hND, hNs, K, hK, hNK, hNfamily⟩

end PoincareConjecture.M47
