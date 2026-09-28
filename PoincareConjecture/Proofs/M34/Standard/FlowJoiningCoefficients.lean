import PoincareConjecture.Proofs.M34.Standard.EuclideanFlowEvolution
import PoincareConjecture.Proofs.M34.Standard.JoinedEvolutionBootstrap
import PoincareConjecture.Proofs.M34.Mathlib.TimeSliceGluing











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.FlowJoining

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {S τ : ℝ}
  (G : RicciFlow 3 StandardCapSpace (Icc 0 S))
  (H : RicciFlow 3 StandardCapSpace (Ico 0 τ))



noncomputable def coefficients (p : ℝ × StandardCapSpace) : MetricCoefficient 3 :=
  if p.1 < S then (G.metric p.1).euclideanCoefficients p.2
  else (H.metric (p.1 - S)).euclideanCoefficients p.2



theorem coefficients_of_lt {t : ℝ} (ht : t < S) (x : StandardCapSpace) :
    coefficients G H (t, x) = (G.metric t).euclideanCoefficients x := by
  simp only [coefficients, ht, if_true]



theorem coefficients_of_le {t : ℝ} (ht : S ≤ t) (x : StandardCapSpace) :
    coefficients G H (t, x) = (H.metric (t - S)).euclideanCoefficients x := by
  simp only [coefficients, not_lt.mpr ht, if_false]



theorem finiteSpatialJet_of_lt (m : ℕ) {t : ℝ} (ht : t < S) (x : StandardCapSpace) :
    spatialJet m (coefficients G H) (t, x) = spatialJet m
      (fun p : ℝ × StandardCapSpace => (G.metric p.1).euclideanCoefficients p.2) (t, x) := by
  funext j
  simp only [spatialJet, coefficients_of_lt G H ht]



theorem finiteSpatialJet_of_le (m : ℕ) {t : ℝ} (ht : S ≤ t) (x : StandardCapSpace) :
    spatialJet m (coefficients G H) (t, x) = spatialJet m
      (fun p : ℝ × StandardCapSpace => (H.metric p.1).euclideanCoefficients p.2)
      (t - S, x) := by
  funext j
  simp only [spatialJet, coefficients_of_le G H ht]



theorem past_coefficients_smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × StandardCapSpace =>
      (G.metric p.1).euclideanCoefficients p.2) (Ioc 0 S ×ˢ univ) :=
  G.contDiffOn_euclideanCoefficients.mono (prod_mono Ioc_subset_Icc_self (Subset.refl univ))



theorem future_coefficients_smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × StandardCapSpace =>
      (H.metric (p.1 - S)).euclideanCoefficients p.2) (Ico S (S + τ) ×ˢ univ) := by
  have hpath : ContDiff ℝ ∞ (fun p : ℝ × StandardCapSpace => (p.1 - S, p.2)) := by
    fun_prop
  apply H.contDiffOn_euclideanCoefficients.comp hpath.contDiffOn
  intro p hp
  exact ⟨⟨sub_nonneg.mpr hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩



theorem coefficients_smooth_off_time :
    ContDiffOn ℝ ∞ (coefficients G H) ((Ioo 0 (S + τ) \ {S}) ×ˢ univ) :=
  contDiffOn_time_ite_off_time (past_coefficients_smooth G) (future_coefficients_smooth H)



theorem continuousOn_spatialJet (hinit : H.metric 0 = G.metric S) (m : ℕ) :
    ContinuousOn (fun p : ℝ × StandardCapSpace =>
      iteratedFDeriv ℝ m (fun x => coefficients G H (p.1, x)) p.2)
      (Ioo 0 (S + τ) ×ˢ univ) := by
  apply continuousOn_spatialJet_time_ite
    (past_coefficients_smooth G) (future_coefficients_smooth H)
  intro x
  simp only [sub_self, hinit]




theorem spatialJet_mem_domain (t : ℝ) (x : StandardCapSpace) :
    spatialJet 2 (coefficients G H) (t, x) ∈ jetRicciFlowDomain 3 := by
  by_cases ht : t < S
  · rw [finiteSpatialJet_of_lt G H 2 ht]
    exact G.euclideanSpatialJet_mem_domain t x
  · rw [finiteSpatialJet_of_le G H 2 (not_lt.mp ht)]
    exact H.euclideanSpatialJet_mem_domain (t - S) x

variable (hS : 0 < S) (hτ : 0 < τ)

include hS hτ

set_option synthInstance.maxHeartbeats 100000 in



theorem deriv_coefficients_eq_operator_off_time {t : ℝ}
    (ht : t ∈ Ioo 0 (S + τ)) (hne : t ≠ S) (x : StandardCapSpace) :
    deriv (fun s => coefficients G H (s, x)) t =
      jetRicciFlowOperator 3 (spatialJet 2 (coefficients G H) (t, x)) := by
  have hnS : (Ioo 0 S).Nontrivial := by
    refine ⟨S / 3, ⟨?_, ?_⟩, 2 * S / 3, ⟨?_, ?_⟩, ?_⟩ <;> linarith
  have hnτ : (Ioo 0 τ).Nontrivial := by
    refine ⟨τ / 3, ⟨?_, ?_⟩, 2 * τ / 3, ⟨?_, ?_⟩, ?_⟩ <;> linarith
  by_cases htS : t < S
  · let G' := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G
      Ioo_subset_Icc_self ordConnected_Ioo hnS
    have hd := G'.hasDerivAt_euclideanCoefficients isOpen_Ioo ⟨ht.1, htS⟩ x
    have heq : (fun s => coefficients G H (s, x)) =ᶠ[𝓝 t]
        (fun s => (G.metric s).euclideanCoefficients x) := by
      filter_upwards [Iio_mem_nhds htS] with s hs
      exact coefficients_of_lt G H hs x
    rw [heq.deriv_eq, finiteSpatialJet_of_lt G H 2 htS]
    exact hd.deriv
  · have hSt : S < t := lt_of_le_of_ne (not_lt.mp htS) (Ne.symm hne)
    let H' := Poincare.Geometry.RicciFlow.Harnack.restrictFlow H
      Ioo_subset_Ico_self ordConnected_Ioo hnτ
    have htime : t - S ∈ Ioo 0 τ := ⟨sub_pos.mpr hSt, by linarith [ht.2]⟩
    have hd := H'.hasDerivAt_euclideanCoefficients isOpen_Ioo htime x
    have hpath : HasDerivAt (fun s : ℝ => s - S) 1 t := (hasDerivAt_id t).sub_const S
    have hc := hd.scomp t hpath
    have heq : (fun s => coefficients G H (s, x)) =ᶠ[𝓝 t]
        (fun s => (H.metric (s - S)).euclideanCoefficients x) := by
      filter_upwards [Ioi_mem_nhds hSt] with s hs
      exact coefficients_of_le G H hs.le x
    rw [heq.deriv_eq, finiteSpatialJet_of_le G H 2 hSt.le]
    have h := hc.deriv
    simp only [one_smul] at h
    convert! h using 1

set_option synthInstance.maxHeartbeats 100000 in



theorem coefficients_smooth_interior (hinit : H.metric 0 = G.metric S) :
    ContDiffOn ℝ ∞ (coefficients G H) (Ioo 0 (S + τ) ×ˢ univ) :=
  contDiffOn_of_joined_spatial_jet_evolution
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3)
    (coefficients_smooth_off_time G H) (continuousOn_spatialJet G H hinit)
    (fun p _ => spatialJet_mem_domain G H p.1 p.2)
    (fun p hp => deriv_coefficients_eq_operator_off_time G H hS hτ hp.1.1 hp.1.2 p.2)

set_option synthInstance.maxHeartbeats 100000 in



theorem hasDerivAt_coefficients (hinit : H.metric 0 = G.metric S)
    {t : ℝ} (ht : t ∈ Ioo 0 (S + τ)) (x : StandardCapSpace) :
    HasDerivAt (fun s => coefficients G H (s, x))
      (jetRicciFlowOperator 3 (spatialJet 2 (coefficients G H) (t, x))) t :=
  hasDerivAt_of_joined_spatial_jet_evolution
    (p := (t, x))
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3)
    (coefficients_smooth_off_time G H) (continuousOn_spatialJet G H hinit)
    (fun p _ => spatialJet_mem_domain G H p.1 p.2)
    (fun p hp => deriv_coefficients_eq_operator_off_time G H hS hτ hp.1.1 hp.1.2 p.2)
    ⟨ht, mem_univ x⟩

end PoincareConjecture.M34.FlowJoining
