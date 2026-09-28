import PoincareConjecture.Proofs.M34.Thm12_5_Existence.TerminalReversal
import PoincareConjecture.Proofs.M34.Standard.InitialEvolutionBootstrap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

set_option synthInstance.maxHeartbeats 100000 in

theorem partialFlow_hasDerivAt_coefficients {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) {t : ℝ} (ht : t ∈ Ioo 0 F.lifetime)
    (x : StandardCapSpace) :
    HasDerivAt (fun s => (F.flow.metric s).euclideanCoefficients x)
      (jetRicciFlowOperator 3 (spatialJet 2
        (fun p : ℝ × StandardCapSpace => (F.flow.metric p.1).euclideanCoefficients p.2)
        (t, x))) t := by
  have hne : (Ioo 0 F.lifetime).Nontrivial := by
    refine ⟨F.lifetime / 3, ⟨?_, ?_⟩, 2 * F.lifetime / 3, ⟨?_, ?_⟩, ?_⟩ <;>
      linarith [F.lifetime_pos]
  let H := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F.flow
    Ioo_subset_Ico_self ordConnected_Ioo hne
  have hinv (y : StandardCapSpace) (_hy : y ∈ (univ : Set StandardCapSpace)) :
      (mfderiv (𝓡 3) (𝓡 3) id y).IsInvertible := by
    rw [mfderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have heq := deriv_pullbackCoefficients_eq_ricciFlowOperator H isOpen_Ioo isOpen_univ
    contMDiffOn_id hinv ht (mem_univ x)
  simp only [RiemannianMetric.pullbackCoefficients_id] at heq
  have hreg := (partialFlow_contDiffOn_coefficients F).mono
    (prod_mono Ioo_subset_Ico_self (Subset.refl univ))
  have hpoint := hreg.contDiffAt (x := (t, x))
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hd := (hpoint.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
    (by simp)
  have hder := hd.hasDerivAt
  rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
  convert! hder using 1
  exact heq.symm

namespace PartialFlowTerminalJets

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S)

set_option synthInstance.maxHeartbeats 100000 in

theorem reverseFiniteSpatialJet_of_pos (m : ℕ) {t : ℝ} (ht : 0 < t)
    (x : StandardCapSpace) :
    spatialJet m L.reverseCoefficients (t, x) = spatialJet m
      (fun p : ℝ × StandardCapSpace => (F.flow.metric p.1).euclideanCoefficients p.2)
      (S - t, x) := by
  funext j
  exact L.reverseSpatialJet_of_pos j ht x

set_option synthInstance.maxHeartbeats 100000 in

theorem reverseSpatialJet_mem_domain (P : RicciFlowCurvatureTheory.{0})
    (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    (t : ℝ) (x : StandardCapSpace) :
    spatialJet 2 L.reverseCoefficients (t, x) ∈ jetRicciFlowDomain 3 := by
  change ((twoJetProjection 3 (spatialJet 2 L.reverseCoefficients (t, x))).1).IsInvertible
  rw [twoJetProjection_spatialJet]
  change (L.reverseCoefficients (t, x)).IsInvertible
  by_cases ht : 0 < t
  · rw [L.reverseCoefficients_of_pos ht]
    convert! (F.flow.metric (S - t)).inner_isInvertible x
  · simp only [reverseCoefficients, ht, if_false]
    convert! (L.metric P E0 hS hSF hB hfull).inner_isInvertible x

set_option synthInstance.maxHeartbeats 100000 in

theorem deriv_reverseCoefficients_eq_neg_operator (hSF : S ≤ F.lifetime)
    {t : ℝ} (ht : t ∈ Ioo 0 S) (x : StandardCapSpace) :
    deriv (fun r => L.reverseCoefficients (r, x)) t =
      -jetRicciFlowOperator 3 (spatialJet 2 L.reverseCoefficients (t, x)) := by
  have htime : S - t ∈ Ioo 0 F.lifetime :=
    ⟨sub_pos.mpr ht.2, (sub_lt_self S ht.1).trans_le hSF⟩
  have hd := partialFlow_hasDerivAt_coefficients F htime x
  have hr : HasDerivAt (fun r : ℝ => S - r) (-1) t := by
    convert! (hasDerivAt_id t).const_sub S using 1
  have hcomp := hd.scomp t hr
  have heq : (fun r => L.reverseCoefficients (r, x)) =ᶠ[𝓝 t]
      (fun r => (F.flow.metric (S - r)).euclideanCoefficients x) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht.1] with r hr
    exact L.reverseCoefficients_of_pos hr x
  rw [heq.deriv_eq, L.reverseFiniteSpatialJet_of_pos 2 ht.1]
  have h := hcomp.deriv
  simp only [neg_smul, one_smul] at h
  convert! h using 1

variable (P : RicciFlowCurvatureTheory.{0}) (E0 : StandardCapEstimate g0)
  {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)

include P E0 hS hSF hB hfull

set_option synthInstance.maxHeartbeats 100000 in

theorem contDiffOn_reverseSpatialJet (m : ℕ) :
    ContDiffOn ℝ ∞ (L.reverseSpatialJet m) (Ico 0 S ×ˢ univ) :=
  contDiffOn_spatialJets_of_initial_evolution
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3).neg
    (L.contDiffOn_reverseCoefficients_interior hSF)
    (L.continuousOn_reverseSpatialJet P E0 hS hSF hB hfull)
    (fun p _ => L.reverseSpatialJet_mem_domain P E0 hS hSF hB hfull p.1 p.2)
    (fun p hp => L.deriv_reverseCoefficients_eq_neg_operator hSF hp.1 p.2) m

set_option synthInstance.maxHeartbeats 100000 in

theorem contDiffOn_reverseCoefficients :
    ContDiffOn ℝ ∞ L.reverseCoefficients (Ico 0 S ×ˢ univ) :=
  contDiffOn_of_initial_spatial_jet_evolution
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3).neg
    (L.contDiffOn_reverseCoefficients_interior hSF)
    (L.continuousOn_reverseSpatialJet P E0 hS hSF hB hfull)
    (fun p _ => L.reverseSpatialJet_mem_domain P E0 hS hSF hB hfull p.1 p.2)
    (fun p hp => L.deriv_reverseCoefficients_eq_neg_operator hSF hp.1 p.2)

set_option synthInstance.maxHeartbeats 100000 in

theorem hasDerivWithinAt_reverseCoefficients {t : ℝ} (ht : t ∈ Ico 0 S)
    (x : StandardCapSpace) :
    HasDerivWithinAt (fun r => L.reverseCoefficients (r, x))
      (-jetRicciFlowOperator 3 (spatialJet 2 L.reverseCoefficients (t, x))) (Ico 0 S) t :=
  hasDerivWithinAt_of_initial_spatial_jet_evolution (p := (t, x))
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3).neg
    (L.contDiffOn_reverseCoefficients_interior hSF)
    (L.continuousOn_reverseSpatialJet P E0 hS hSF hB hfull)
    (fun p _ => L.reverseSpatialJet_mem_domain P E0 hS hSF hB hfull p.1 p.2)
    (fun p hp => L.deriv_reverseCoefficients_eq_neg_operator hSF hp.1 p.2) ⟨ht, mem_univ x⟩

end PartialFlowTerminalJets
end PoincareConjecture.M34
