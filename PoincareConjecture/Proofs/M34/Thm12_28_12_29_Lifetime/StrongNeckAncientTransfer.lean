import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckSequenceTransfer
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckMetricTransport
import PoincareConjecture.Definitions.M30ControlledBlowupLimits










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M34

private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    MeasurableSpace L.carrier.carrier := L.carrier.measurableSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    BorelSpace L.carrier.carrier := L.carrier.borelSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    T2Space L.carrier.carrier := L.carrier.t2Space
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    T3Space L.carrier.carrier := L.carrier.t3Space
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    SecondCountableTopology L.carrier.carrier := L.carrier.secondCountable
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ConnectedSpace L.carrier.carrier := L.connectedSpace



theorem exists_normalized_limit_neck_of_ancient
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) {kappa delta : ℝ}
    (A : M30AncientKappaIdentification L kappa)
    (N : StrongEvolvingNeck A.certificate.solution 0 delta) (hcenter : N.center = L.base) :
    ∃ N' : EpsilonNeck (L.flow.metric 0), N'.center = L.base ∧ N'.epsilon = delta ∧
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
  let N' := N.terminal_neck.ofMetricEq (A.certificate.metric_eq 0 le_rfl)
  obtain ⟨hepsilon, hNcenter, hcoordinate⟩ :=
    N.terminal_neck.ofMetricEq_data (A.certificate.metric_eq 0 le_rfl)
  refine ⟨N', hNcenter.trans (N.terminal_center.trans hcenter),
    hepsilon.trans N.terminal_epsilon, ?_⟩
  rw [hepsilon, N.terminal_epsilon]
  apply N.metric_comparison.congr_cylinder
  intro s hs z _ v w
  rw [hnscalar, div_one, zero_add, one_mul, A.certificate.metric_eq s hs.2, hcoordinate]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R



theorem ordinaryChapter11_eventually_strongNeck_of_ancient
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop)
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) (blowupBackwardInterval ⊤))
    {kappa delta epsilon : ℝ} (A : M30AncientKappaIdentification C.limit kappa)
    (N : StrongEvolvingNeck A.certificate.solution 0 delta)
    (hcenter : N.center = C.limit.base) (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon < 1 / 2) (hdelta : delta ≤ epsilon / 4) :
    ∀ᶠ k : ℕ in atTop,
      ∃ Ns : GeneralizedStrongNeck (G) (p (C.subsequence k)).1 epsilon,
        Ns.center = (p (C.subsequence k)).2 := by
  obtain ⟨N', hNcenter, hNepsilon, hclose⟩ :=
    exists_normalized_limit_neck_of_ancient C.limit A N hcenter
  have hJ : UniqueDiffOn ℝ (blowupBackwardInterval ⊤) := by
    rw [A.domain_eq]
    exact uniqueDiffOn_Iic _
  have hJI : Icc (-1 : ℝ) 0 ⊆ blowupBackwardInterval ⊤ := by
    rw [A.domain_eq]
    exact fun _ hs => hs.2
  exact ordinaryChapter11_eventually_centered_strongNeck R p hpositive hdiverges C
    hJ hJI N' hNcenter hepsilon hepsilonHalf (hNepsilon.trans_le hdelta) hclose

end PoincareConjecture.M34
