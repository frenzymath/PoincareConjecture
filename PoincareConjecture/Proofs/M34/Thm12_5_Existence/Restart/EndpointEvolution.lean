import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.LimitEvolution
import PoincareConjecture.Proofs.M34.Standard.InitialEvolutionBootstrap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.MetricInteriorCoefficientLimit

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)]
  {A : MetricFlowApproximation ginit Mfamily}
  (G : MetricInteriorCoefficientLimit A)

theorem contDiffOn_closedCoefficients_interior :
    ContDiffOn ℝ ∞ G.closedCoefficients (Ioo 0 A.time ×ˢ univ) := by
  apply G.smooth.congr
  intro p hp
  exact G.closedCoefficients_of_mem hp.1 p.2

theorem contDiff_closedCoefficients_slice (t : ℝ) :
    ContDiff ℝ ∞ (fun x => G.closedCoefficients (t, x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases ht : t ∈ Ioo 0 A.time
  · have h := (G.smooth.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)).comp x
        (contDiffAt_const.prodMk contDiffAt_id)
    simpa only [closedCoefficients, ht, if_true, Function.comp_def, id_eq] using h
  · simpa only [closedCoefficients, ht, if_false] using
      ginit.contDiffAt_euclideanCoefficients x

set_option synthInstance.maxHeartbeats 100000 in

theorem closedFiniteSpatialJet_of_mem (m : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 A.time)
    (x : StandardCapSpace) :
    spatialJet m G.closedCoefficients (t, x) = spatialJet m G.coefficients (t, x) := by
  funext j
  exact G.closedSpatialJet_of_mem j ht x

set_option synthInstance.maxHeartbeats 100000 in

theorem closedSpatialJet_mem_domain (P : RicciFlowCurvatureTheory.{0})
    (t : ℝ) (x : StandardCapSpace) :
    spatialJet 2 G.closedCoefficients (t, x) ∈ jetRicciFlowDomain 3 := by
  by_cases ht : t ∈ Ioo 0 A.time
  · rw [G.closedFiniteSpatialJet_of_mem 2 ht]
    exact G.spatialJet_mem_domain P ht x
  · change ((twoJetProjection 3 (spatialJet 2 G.closedCoefficients (t, x))).1).IsInvertible
    rw [twoJetProjection_spatialJet]
    change (G.closedCoefficients (t, x)).IsInvertible
    simp only [closedCoefficients, ht, if_false]
    convert! ginit.inner_isInvertible x

set_option synthInstance.maxHeartbeats 100000 in

theorem deriv_closedCoefficients_eq_operator (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ioo 0 A.time) (x : StandardCapSpace) :
    deriv (fun s => G.closedCoefficients (s, x)) t =
      jetRicciFlowOperator 3 (spatialJet 2 G.closedCoefficients (t, x)) := by
  have heq : (fun s => G.closedCoefficients (s, x)) =ᶠ[𝓝 t]
      (fun s => G.coefficients (s, x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact G.closedCoefficients_of_mem hs x
  rw [heq.deriv_eq, G.closedFiniteSpatialJet_of_mem 2 ht]
  exact G.deriv_coefficients_eq_operator P ht x

set_option synthInstance.maxHeartbeats 100000 in

theorem contDiffOn_closedSpatialJet (P : RicciFlowCurvatureTheory.{0}) (m : ℕ) :
    ContDiffOn ℝ ∞ (G.closedSpatialJet m) (Ico 0 A.time ×ˢ univ) :=
  contDiffOn_spatialJets_of_initial_evolution
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3)
    G.contDiffOn_closedCoefficients_interior (G.continuousOn_closedSpatialJet P)
    (fun p _ => G.closedSpatialJet_mem_domain P p.1 p.2)
    (fun p hp => G.deriv_closedCoefficients_eq_operator P hp.1 p.2) m

set_option synthInstance.maxHeartbeats 100000 in

theorem contDiffOn_closedCoefficients (P : RicciFlowCurvatureTheory.{0}) :
    ContDiffOn ℝ ∞ G.closedCoefficients (Ico 0 A.time ×ˢ univ) :=
  contDiffOn_of_initial_spatial_jet_evolution
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3)
    G.contDiffOn_closedCoefficients_interior (G.continuousOn_closedSpatialJet P)
    (fun p _ => G.closedSpatialJet_mem_domain P p.1 p.2)
    (fun p hp => G.deriv_closedCoefficients_eq_operator P hp.1 p.2)

set_option synthInstance.maxHeartbeats 100000 in

theorem hasDerivWithinAt_closedCoefficients (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ico 0 A.time) (x : StandardCapSpace) :
    HasDerivWithinAt (fun s => G.closedCoefficients (s, x))
      (jetRicciFlowOperator 3 (spatialJet 2 G.closedCoefficients (t, x))) (Ico 0 A.time) t :=
  hasDerivWithinAt_of_initial_spatial_jet_evolution
    (p := (t, x))
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3)
    G.contDiffOn_closedCoefficients_interior (G.continuousOn_closedSpatialJet P)
    (fun p _ => G.closedSpatialJet_mem_domain P p.1 p.2)
    (fun p hp => G.deriv_closedCoefficients_eq_operator P hp.1 p.2) ⟨ht, mem_univ x⟩

end PoincareConjecture.M34.MetricInteriorCoefficientLimit
