import PoincareConjecture.Proofs.M35.CapGeometry.SelectedFullStandardNeck
import PoincareConjecture.Proofs.M35.Thm12_28.LimitStrongNeckTransfer
import PoincareConjecture.Proofs.M35.Thm12_28.NeckCompactness









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem scalar_eq_of_equal_metrics
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    {g h : RiemannianMetric 3 M} (heq : g = h)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    D.scalarCurvature x = D'.scalarCurvature x := by
  subst h
  exact D.scalarCurvature_eq D' x



theorem blowupSequence_limit_full_neck_canonical (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (kappa : ℝ)
    (A : BlowupAncientKappaIdentification L.limit kappa) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ (epsilon : ℝ) (N : StrongEvolvingNeck A.solution 0 epsilon)
      (_he : epsilon ≤ 1 / 24) (_hcenter : N.center = L.limit.base)
      (j : ℕ) (_hstage : closure N.terminal_neck.carrier ⊆ L.exhaustion.space j) (C : ℝ),
      ∀ᶠ k in atTop, GeneralizedCanonicalControl
        (F := generalizedFlow E.flow.base.flow) (t (L.subsequence k))
        ((sliceDiffeomorph (ht (L.subsequence k))).symm (x (L.subsequence k))) epsilon C := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro epsilon N he hcenter j hstage C
  have hscalar : (A.solution.flow.connection 0).scalarCurvature N.center = 1 := by
    rw [hcenter]
    exact (scalar_eq_of_equal_metrics (A.metric_eq 0 le_rfl)
      (A.solution.flow.connection 0) (L.limit.flow.connection 0) L.limit.base).trans
        L.limit.scalar_normalized
  have hcomparison : RoundCylinderFamilyClose epsilon (Ioc (-1 : ℝ) 0)
      (fun u => roundCylinderPullback (L.limit.flow.metric u) N.terminal_neck.coordinate_map) := by
    apply cylinder_family_congr _ N.metric_comparison
    intro u hu z _ v w
    rw [hscalar, div_one, zero_add, one_mul, A.metric_eq u hu.2]
  have hreturned := blowupSequence_full_standard_evolving_neck P E.atlas E t x ht hR L
    (A.solution.flow.metric 0) N.terminal_neck (A.metric_eq 0 le_rfl)
    (N.terminal_epsilon.symm ▸ he) (N.terminal_center.trans hcenter)
    (N.terminal_neck.isCompact_closure (A.solution.complete 0 le_rfl)) j hstage
    (Ioc (-1 : ℝ) 0) (Icc (-1 : ℝ) 0) isCompact_Icc
    (fun _ hu => hu.2) (fun _ hu => ⟨hu.1.le, hu.2⟩)
    (N.terminal_epsilon.symm ▸ hcomparison)
  filter_upwards [hreturned] with k hk
  obtain ⟨K⟩ := hk
  exact N.terminal_epsilon ▸ K.generalized_canonical_control P subset_rfl

end PoincareConjecture.M35.OrdinaryRealization
