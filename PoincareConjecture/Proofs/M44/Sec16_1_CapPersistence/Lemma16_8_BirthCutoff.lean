import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialSlab
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_GlobalStandardCollar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedSlab
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_InitialExactCutoff
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_SmallHeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

theorem exists_birth_collar_cutoff (P : M44CapPersistencePredecessors.{u})
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    (K : MetricSurgeryConstants) {epsilon C r A : ℝ}
    (hepsilon : 0 < epsilon) (hC : 0 < C) (hr : 0 < r) (hA : 0 < A) :
    ∃ R deltaBar tau M : ℝ, ∃ x u v : E,
      A < R ∧ 2 < R ∧ 0 < deltaBar ∧ 0 < tau ∧ 1 ≤ M ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 → F.local_constants = K →
      F.parameters.epsilon = epsilon → F.parameters.C = C →
      ∀ (a : ℝ) (ha : a ∈ F.surgery_times) [Nonempty (F.slice a).carrier],
      F.parameters.delta a ≤ deltaBar → ∀ (i : Fin (F.event a ha).cap_count) {T : ℝ},
      0 < T → T ≤ tau →
      ∀ S : SurgeryRegularSlab F.slice F.metric a (a + T * F.parameters.h a ^ 2),
      SurgeryFlowPinched F → Icc a (a + T * F.parameters.h a ^ 2) ⊆ F.time_domain →
      SurgeryCanonicalOn F (Ico a (a + T * F.parameters.h a ^ 2)) r →
      ∃ G : RicciFlow 3 (F.slice a).carrier (Icc 0 T),
        (∀ s y w z, (S.flow.metric (a + s * F.parameters.h a ^ 2)).inner y w z =
          F.parameters.h a ^ 2 * (G.metric s).inner y w z) ∧
        ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice a).carrier ∞,
          e.source = F.standard_initial.metric.ball 0 R ∧
          e.target = (G.metric 0).ball ((F.event a ha).caps i).tip R ∧
          (∀ s ∈ Icc (0 : ℝ) T,
            metricTwoJet ((G.metric s).pullbackCoefficients e) x ∈ collarJetRegion C u v) ∧
          (∀ s ∈ Icc (0 : ℝ) T, ∀ y ∈ e.target,
            (G.connection s).scalarCurvature y ≤ 2 * M ∧
            (G.connection s).curvatureTensorNorm y ≤ 13 * max (2 * M) (Real.exp 4)) := by
  obtain ⟨x, u, v, _hcompact, hcollar⟩ :=
    exists_global_standard_collar standard hC (theta := 0) le_rfl zero_lt_one
  have hJ := hcollar 0 ⟨le_rfl, le_rfl⟩
  change metricTwoJet (standard.flow.base.flow.metric 0).euclideanCoefficients x ∈
    collarJetRegion C u v at hJ
  rw [standard.flow.base.initial_metric] at hJ
  let R := |M36.radialArclength g0 ‖x‖| + A + 4
  have hRA : A < R := by dsimp [R]; linarith only [abs_nonneg (M36.radialArclength g0 ‖x‖)]
  have hR : 2 < R := by dsimp [R]; linarith only [abs_nonneg (M36.radialArclength g0 ‖x‖), hA]
  have hx : x ∈ g0.metric.ball 0 (R - 2) := by
    change g0.metric.edist 0 x < ENNReal.ofReal (R - 2)
    rw [M36.standard_edist_zero, ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < R - 2)]
    dsimp only [R]
    linarith only [le_abs_self (M36.radialArclength g0 ‖x‖), hA]
  obtain ⟨d, tau, M, hd, htau, hM, hbound⟩ := exists_initial_slab_bound P g0 C x u v hJ hR hx
  let eta := d / 2
  have heta : 0 < eta := half_pos hd
  obtain ⟨dc, hdc, hcomparison⟩ := exists_initial_cap_exact_comparison_cutoff.{u} g0 K heta
  obtain ⟨dh, hdh, hheight⟩ := exists_surgery_normalization_cutoff hepsilon hr
  refine ⟨R, min dc dh, min 1 tau, M, x, u, v, hRA, hR,
    lt_min hdc hdh, lt_min zero_lt_one htau, hM, ?_⟩
  intro F hg0 hK heps hconstant a ha _ hdelta i T hT hTtau S hpinch hdomain hcanonical
  have ha0 := F.time_domain_nonnegative (F.surgery_times_subset ha)
  have hapos := F.parameters.h_pos a ha0
  obtain ⟨hsmall, hthreshold⟩ := hheight F.parameters heps a ha0
    (hdelta.trans (min_le_right _ _))
  obtain ⟨Q, _hlink, hballs⟩ := hcomparison F hg0 hK a ha (hdelta.trans (min_le_left _ _)) i
  obtain ⟨G, hmetric, hinitial⟩ := exists_normalized_regularSlab_for_bound P F hT
    (sq_pos_of_pos hapos) S
  have hbirth (y) (w z) : (G.metric 0).inner y w z =
      (F.parameters.h a)⁻¹ ^ 2 * (F.metric a).inner y w z := by
    simpa only [inv_pow] using hinitial y w z
  have hq : F.parameters.h a ^ 2 * (r⁻¹ ^ 2) ≤ 1 := by
    simpa only [div_pow, div_eq_mul_inv, mul_pow, inv_pow] using hthreshold
  obtain ⟨e, hsource, htarget, _hmap, hkeep, hcurv⟩ :=
    hbound F hg0 a ha i hT (hTtau.trans (min_le_left _ _))
      (hTtau.trans (min_le_right _ _)) hsmall hq S G (fun s _ => hmetric s) hbirth Q
      (by dsimp [eta]; linarith only [hd]) hballs
      (fun t ht y hy => by
        rw [← hconstant]
        exact hcanonical t ht (hdomain ⟨ht.1, ht.2.le⟩) y hy)
      hpinch hdomain
  exact ⟨G, hmetric, e, hsource, htarget, hkeep, hcurv⟩

end PoincareConjecture.M44
