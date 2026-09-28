import PoincareConjecture.Proofs.M35.CapGeometry.FarTipStrongNeck
import PoincareConjecture.Proofs.M35.CapGeometry.SphereLineNormalizedTime
import PoincareConjecture.Proofs.M35.CapGeometry.CylinderLongerWindow
import PoincareConjecture.Proofs.M35.CapGeometry.SelectedLongerNeck










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "V" => EuclideanSpace ℝ (Fin 3)

private theorem scalar_eq_of_equal_metrics
    {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓡 3) ∞ M]
    {g h : RiemannianMetric 3 M} (heq : g = h)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    D.scalarCurvature x = D'.scalarCurvature x := by
  subst h
  exact D.scalarCurvature_eq D' x



theorem blowupSequence_far_tip_longer_standard_neck
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
    ∀ {delta gamma epsilon C : ℝ},
      M27KappaNine93Conclusion A.solution delta C → 0 < delta → delta ≤ gamma →
      0 < epsilon → epsilon < 1 / 2 → gamma ≤ epsilon / 4 →
      ((⌊gamma⁻¹⌋₊ + 1 : ℕ) : ℝ) *
        (18 + 32 * 2 ^ (⌊gamma⁻¹⌋₊ + 2)) * delta ^ 2 < gamma ^ 2 →
      ∀ᶠ k in atTop, Nonempty (StandardEvolvingNeck E.atlas E.flow (t (L.subsequence k))
        epsilon (x (L.subsequence k)) (Ioc (-(1 + epsilon)) 0)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro delta gamma epsilon C H hdelta hdg he hehalf hge hsmall
  obtain ⟨⟨model⟩, N, hcenter, j, hstage⟩ :=
    blowupSequence_far_tip_centered_strong_neck P E t x ht hR hd L A H
  have hscalar : (A.solution.flow.connection 0).scalarCurvature N.center = 1 := by
    rw [hcenter]
    exact (scalar_eq_of_equal_metrics (A.metric_eq 0 le_rfl)
      (A.solution.flow.connection 0) (L.limit.flow.connection 0) L.limit.base).trans
        L.limit.scalar_normalized
  have hcomparison : RoundCylinderFamilyClose delta (Ioc (-1 : ℝ) 0)
      (fun u => roundCylinderPullback (L.limit.flow.metric u) N.terminal_neck.coordinate_map) := by
    apply cylinder_family_congr _ N.metric_comparison
    intro u hu z _ v w
    rw [hscalar, div_one, zero_add, one_mul, A.metric_eq u hu.2]
  have haffine : ∀ u ≤ 0, ∀ z v w,
      roundCylinderPullback (L.limit.flow.metric u) N.terminal_neck.coordinate_map z v w =
        (1 + 2 * u) * roundCylinderPullback (L.limit.flow.metric 0)
          N.terminal_neck.coordinate_map z v w -
        2 * u * roundCylinderPullback (L.limit.flow.metric (-1 / 2))
          N.terminal_neck.coordinate_map z v w := by
    intro u hu z v w
    have h := sphereLine_normalized_family_affine model N.terminal_neck.coordinate_map
      1 zero_lt_one u hu z v w
    simpa only [div_one, one_mul, A.metric_eq u hu, A.metric_eq 0 le_rfl,
      A.metric_eq (-1 / 2) (by norm_num)] using h
  have hlong := hcomparison.extend_affine_window hdelta hdg epsilon
    (by linarith) hsmall haffine
  exact blowupSequence_longer_standard_evolving_neck P E.atlas E t x ht hR L
    (A.solution.flow.metric 0) N.terminal_neck (N.terminal_center.trans hcenter)
    j hstage gamma epsilon (hdelta.trans_le hdg) he hehalf
    (N.terminal_epsilon.trans_le hdg) hge hlong




theorem blowupSequence_far_tip_prescribed_window
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) {kappa : ℝ}
    (A : BlowupAncientKappaIdentification L.limit kappa)
    (epsilon : ℝ) (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    ∀ᶠ k in atTop, Nonempty (StandardEvolvingNeck E.atlas E.flow (t (L.subsequence k))
      epsilon (x (L.subsequence k)) (Ioc (-(1 + epsilon)) 0)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  obtain ⟨epsilonBar, hbar, hmodels⟩ := P.kappa_models.theorem_9_93
  have hgamma : 0 < epsilon / 4 := div_pos he (by norm_num)
  obtain ⟨delta, hdelta, hdg, hdb, hsmall⟩ :=
    exists_affine_window_accuracy (epsilon / 4) (epsilonBar / 2) hgamma (by positivity)
  have hdeltaBar : delta < epsilonBar := hdb.trans_lt (by linarith)
  obtain ⟨C, _hC, hCmodels⟩ := hmodels delta hdelta hdeltaBar
  exact blowupSequence_far_tip_longer_standard_neck P E t x ht hR hd L A
    (hCmodels A.solution).alternatives hdelta hdg he hehalf le_rfl hsmall

end PoincareConjecture.M35.OrdinaryRealization
