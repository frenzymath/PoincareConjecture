import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticTolerance
import PoincareConjecture.Proofs.M44.Mathlib.CompactTimeModulus










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M47

open SpacetimeBounds SpacetimeBounds.Bootstrap

local notation "E" => StandardCapSpace
local notation "J4" => Jet E (MetricCoefficient 3) 4

noncomputable local instance standardTimeCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance standardTimeCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace



theorem standard_metric_jets_uniform_time_delta {g0 : StandardInitialMetric}
    (S : MaximalStandardCapFlow g0) {theta : ℝ} (htheta : theta < S.base.lifetime)
    {K : Set E} (hK : IsCompact K) (m : ℕ) {nu : ℝ} (hnu : 0 < nu) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc 0 theta, ∀ v ∈ Icc 0 theta,
      |s - v| < delta → ∀ x ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (S.metric s).euclideanCoefficients x -
          iteratedFDeriv ℝ j (S.metric v).euclideanCoefficients x‖ < nu := by
  classical
  have hsub : Icc (0 : ℝ) theta ×ˢ K ⊆ Ico 0 S.base.lifetime ×ˢ (univ : Set E) :=
    fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt htheta⟩, mem_univ _⟩
  have hc (j : Fin (m + 1)) : ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ j.val (S.metric p.1).euclideanCoefficients p.2)
      (Icc 0 theta ×ˢ K) := (M44.continuousOn_standard_spatialJet S.base j).mono hsub
  choose d hd hmod using fun j : Fin (m + 1) =>
    (hc j).exists_uniform_time_delta isCompact_Icc hK hnu
  let delta := Finset.univ.inf' Finset.univ_nonempty d
  have hdelta : 0 < delta := (Finset.lt_inf'_iff _).mpr (fun j _ => hd j)
  refine ⟨delta, hdelta, ?_⟩
  intro s hs v hv hnear x hx j hj
  let i : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hsmall : |s - v| < d i := hnear.trans_le (Finset.inf'_le d (Finset.mem_univ i))
  simpa only [dist_eq_norm] using hmod i s hs v hv hsmall x hx



theorem standard_analytic_uniform_time_delta {g0 : StandardInitialMetric}
    (S : MaximalStandardCapFlow g0) {theta : ℝ} (htheta : theta < S.base.lifetime)
    {K : Set E} (hK : IsCompact K) {nu : ℝ} (hnu : 0 < nu) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc 0 theta, ∀ v ∈ Icc 0 theta,
      |s - v| < delta → ∀ x ∈ K,
        ‖((S.connection s).scalarCurvature x,
            scalarGradientNorm (S.metric s) (S.connection s) x,
            (S.connection s).laplacian (S.connection s).scalarCurvature x +
              2 * (S.connection s).ricciNormSq x) -
          ((S.connection v).scalarCurvature x,
            scalarGradientNorm (S.metric v) (S.connection v) x,
            (S.connection v).laplacian (S.connection v).scalarCurvature x +
              2 * (S.connection v).ricciNormSq x)‖ < nu := by
  let jet : ℝ × E → J4 :=
    spatialJet 4 (fun p : ℝ × E => (S.metric p.1).euclideanCoefficients p.2)
  have hsub : Icc (0 : ℝ) theta ×ˢ K ⊆ Ico 0 S.base.lifetime ×ˢ (univ : Set E) :=
    fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt htheta⟩, mem_univ _⟩
  have hjet : ContinuousOn jet (Icc 0 theta ×ˢ K) := by
    apply continuousOn_pi.mpr
    intro j
    exact (M44.continuousOn_standard_spatialJet S.base j).mono hsub
  have hcont : ContinuousOn (fun p => M34.scalarAnalyticJet 3 (jet p))
      (Icc 0 theta ×ˢ K) :=
    (M34.continuousOn_scalarAnalyticJet 3).comp hjet
      (fun p _ => M34.metric_spatialJet_mem_curvatureJetDomain (S.metric p.1) 2 p.2)
  have hread (s : ℝ) (x : E) : M34.scalarAnalyticJet 3 (jet (s, x)) =
      ((S.connection s).scalarCurvature x,
        scalarGradientNorm (S.metric s) (S.connection s) x,
        (S.connection s).laplacian (S.connection s).scalarCurvature x +
          2 * (S.connection s).ricciNormSq x) := by
    change M34.scalarAnalyticJet 3 (spatialJet 4
      (fun p : ℝ × E => (S.metric s).euclideanCoefficients p.2) (0, x)) = _
    simpa only [scalarGradientNorm_eq_tangentNorm]
      using M34.scalarAnalyticJet_spatialJet (S.connection s) x
  obtain ⟨delta, hdelta, hmod⟩ := hcont.exists_uniform_time_delta isCompact_Icc hK hnu
  refine ⟨delta, hdelta, ?_⟩
  intro s hs v hv hnear x hx
  have h := hmod s hs v hv hnear x hx
  simpa only [dist_eq_norm, hread] using h

end PoincareConjecture.Proofs.M47
