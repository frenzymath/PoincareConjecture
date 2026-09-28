import PoincareConjecture.Proofs.M35.CapGeometry.BlowupNullPlane
import PoincareConjecture.Proofs.M35.Thm12_28.LimitAlternatives
import PoincareConjecture.Proofs.Ch01.CurvatureConnection









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "V" => EuclideanSpace ℝ (Fin 3)

private theorem null_plane_of_metric_eq
    {M : Type*} [TopologicalSpace M] [ChartedSpace V M]
    [IsManifold (𝓡 3) ∞ M] {g h : RiemannianMetric 3 M}
    (heq : g = h) (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M)
    (hnull : ∃ u v : TangentSpace (𝓡 3) x,
      g.inner x u u = 1 ∧ g.inner x v v = 1 ∧ g.inner x u v = 0 ∧
      D.curvatureTensor x u v u v = 0) :
    ∃ u v : TangentSpace (𝓡 3) x,
      h.inner x u u = 1 ∧ h.inner x v v = 1 ∧ h.inner x u v = 0 ∧
      D'.curvatureTensor x u v u v = 0 := by
  cases heq
  obtain ⟨u, v, hu, hv, huv, hR⟩ := hnull
  exact ⟨u, v, hu, hv, huv, (D'.curvatureTensor_eq D x u v u v).trans hR⟩




theorem blowupSequence_far_tip_product_models
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) {kappa : ℝ}
    (A : BlowupAncientKappaIdentification L.limit kappa) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ {epsilon C : ℝ}, M27KappaNine93Conclusion A.solution epsilon C →
      Nonempty (M27SphereLineFlowCertificate A.solution) ∨
        Nonempty (M27TwistedSphereLineFlowCertificate A.solution) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro epsilon C H
  obtain ⟨u, v, hu, hv, huv, hzero⟩ := null_plane_of_metric_eq (A.metric_eq 0 le_rfl).symm
    (L.limit.flow.connection 0) (A.solution.flow.connection 0) L.limit.base
    (blowupSequence_far_tip_exists_null_plane P E t x ht hR hd L)
  have hnotpos : ¬M27PositiveSectionalCurvature A.solution 0 := by
    intro hpos
    have h := hpos L.limit.base u v hu hv huv
    unfold LeviCivitaData.sectionalCurvature at h
    rw [hu, hv, huv, hzero] at h
    norm_num at h
  have hnoncompact := blowupSequence_limit_noncompact P E t x ht hR L
  cases H with
  | round _ quotient =>
      apply False.elim
      apply hnoncompact
      rw [← Set.range_eq_univ.mpr quotient.cover_surjective]
      exact isCompact_range quotient.cover_local_diffeomorph.contMDiff.continuous
  | compactPositive geometry => exact (hnoncompact geometry.compact).elim
  | doubleCapped _ positive _ _ => exact (hnotpos positive).elim
  | cappedEuclidean _ positive _ _ => exact (hnotpos positive).elim
  | cappedQuotient model _ _ => exact Or.inr ⟨model⟩
  | sphereLine model _ => exact Or.inl ⟨model⟩
  | projectivePlaneLine model =>
      exact (blowupSequence_limit_not_projective P E t x ht hR L A ⟨model⟩).elim

end PoincareConjecture.M35.OrdinaryRealization
