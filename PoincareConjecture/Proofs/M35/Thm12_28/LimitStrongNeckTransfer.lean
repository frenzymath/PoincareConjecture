import PoincareConjecture.Proofs.M35.Thm12_28.SelectedStandardNeck
import PoincareConjecture.Proofs.M35.Thm12_28.GeneralizedNeck
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderLocality
import PoincareConjecture.Proofs.Ch01.CurvatureConnection










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem scalar_eq_of_metric_eq
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    {g g' : RiemannianMetric 3 M} (hg : g = g')
    (D : LeviCivitaData g) (D' : LeviCivitaData g') (x : M) :
    D.scalarCurvature x = D'.scalarCurvature x := by
  subst g'
  exact D.scalarCurvature_eq D' x




theorem blowupSequence_limit_neck_canonical (P : M35StandardCapPredecessors)
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
    ∀ (delta : ℝ) (N : StrongEvolvingNeck A.solution 0 delta)
      (_hcenter : N.center = L.limit.base)
      (j : ℕ) (_hstage : closure N.terminal_neck.carrier ⊆ L.exhaustion.space j)
      (epsilon C : ℝ) (_he : 0 < epsilon) (_hehalf : epsilon < 1 / 2)
      (_hde : delta ≤ epsilon / 4),
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
  intro delta N hcenter j hstage epsilon C he hehalf hde
  have hscalar : (A.solution.flow.connection 0).scalarCurvature N.center = 1 := by
    rw [hcenter]
    exact (scalar_eq_of_metric_eq (A.metric_eq 0 le_rfl)
      (A.solution.flow.connection 0) (L.limit.flow.connection 0) L.limit.base).trans
        L.limit.scalar_normalized
  have hcomparison : RoundCylinderFamilyClose delta (Ioc (-1 : ℝ) 0)
      (fun u => roundCylinderPullback (L.limit.flow.metric u) N.terminal_neck.coordinate_map) := by
    apply cylinder_family_congr _ N.metric_comparison
    intro u hu z _ v w
    rw [hscalar, div_one, zero_add, one_mul, A.metric_eq u hu.2]
  have hreturned := blowupSequence_standard_evolving_neck P E.atlas E t x ht hR L
    (A.solution.flow.metric 0) N.terminal_neck (N.terminal_center.trans hcenter) j hstage
    epsilon he hehalf (by rw [N.terminal_epsilon]; exact hde)
    (by rw [N.terminal_epsilon]; exact hcomparison)
  filter_upwards [hreturned] with k hk
  obtain ⟨K⟩ := hk
  exact K.generalized_canonical_control P subset_rfl

end PoincareConjecture.M35.OrdinaryRealization
