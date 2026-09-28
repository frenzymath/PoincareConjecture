import PoincareConjecture.Proofs.M47.CanonicalCapNearbyNeck
import PoincareConjecture.Proofs.M47.CanonicalStandardMetricBounds
import PoincareConjecture.Proofs.M47.BlowupControlsCapPhysicalCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

theorem exists_standard_nearby_metric_factor {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta Lambda : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) (hLambda : 1 < Lambda) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc 0 theta, ∀ v ∈ Icc 0 theta,
      |s - v| < delta → ∀ x : StandardCapSpace, ∀ w : TangentSpace (𝓡 3) x,
        (standard.flow.metric s).tangentNorm x w ≤
          Lambda * (standard.flow.metric v).tangentNorm x w ∧
        (standard.flow.metric v).tangentNorm x w ≤
          Lambda * (standard.flow.metric s).tangentNorm x w := by
  obtain ⟨K, hK, hbound⟩ := exists_standard_slab_metric_bound standard htheta0 htheta
  refine ⟨Real.log Lambda / K, div_pos (Real.log_pos hLambda) hK, ?_⟩
  intro s hs v hv hnear x w
  have hexp : Real.exp (K * |s - v|) ≤ Lambda := by
    calc
      _ ≤ Real.exp (Real.log Lambda) := Real.exp_le_exp.mpr (by
        have h := (le_div_iff₀ hK).mp hnear.le
        nlinarith only [h])
      _ = Lambda := Real.exp_log (zero_lt_one.trans hLambda)
  refine ⟨(hbound v hv s hs x w).trans
    (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _)), ?_⟩
  have h := hbound s hs v hv x w
  rw [abs_sub_comm v s] at h
  exact h.trans (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _))

theorem exists_actualCap_nearby_physical_certificate_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A v : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (hv : v ∈ Icc 0 theta)
    (N : CapCertificate (standard.flow.metric v))
    (hconnection : N.connection = standard.flow.connection v)
    (hsource : N.carrier ⊆ g0.metric.ball 0 A) :
    ∃ eta0 delta : ℝ, 0 < eta0 ∧ 0 < delta ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J),
      s ≤ theta → |s - v| < delta →
      let q := actualCapSliceChart e initial comparison s hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      ∃ H : CapCertificate (F.metric (t + s / Q)),
        H.epsilon = N.epsilon ∧ H.cap_constant = N.cap_constant ∧
        H.connection = F.connection (t + s / Q) ∧
        H.core = q '' N.core ∧ H.carrier = q '' N.carrier := by
  have hvtime : v ∈ Ico 0 standard.flow.base.lifetime := by
    rw [standard.lifetime_one]
    exact ⟨hv.1, hv.2.trans_lt htheta⟩
  have hRic (x : StandardCapSpace) (w : TangentSpace (𝓡 3) x) :
      0 ≤ N.connection.ricci x w w := by
    rw [hconnection]
    exact M04.nonneg_ricci_of_nonnegativeSectionalAt (standard.flow.connection v) x
      (standard.nonnegative_sectional v hvtime x) w
  obtain ⟨Lambda, hLambda, nu, hnu, hcap⟩ := exists_cap_image_certificate_tolerance N
    (standard.complete v hvtime) hRic
  let L := Real.sqrt Lambda
  have hL : 1 < L := by
    simpa only [Real.sqrt_one] using (Real.sqrt_lt_sqrt (by norm_num) hLambda)
  have hLpos : 0 < L := zero_lt_one.trans hL
  have hLsq : L * L = Lambda := Real.mul_self_sqrt (zero_lt_one.trans hLambda).le
  obtain ⟨deltaM, hdeltaM, hmetricTime⟩ :=
    exists_standard_nearby_metric_factor standard (hv.1.trans hv.2) htheta hL
  obtain ⟨etaA, deltaA, hetaA, hdeltaA, hanalytic⟩ :=
    exists_actualCap_nearby_analytic_tolerance standard htheta hA hnu
  obtain ⟨etaE, deltaE, hetaE, hdeltaE, hneckE⟩ :=
    exists_actualCap_nearby_image_neck_tolerance standard htheta hA hv N.end_neck
      (N.end_neck_connection.trans hconnection) (N.end_neck_subset.trans hsource)
  obtain ⟨etaB, deltaB, hetaB, hdeltaB, hneckB⟩ :=
    exists_actualCap_nearby_image_neck_tolerance standard htheta hA hv N.boundary_neck
      (N.boundary_neck_connection.trans hconnection) (N.boundary_neck_subset.trans hsource)
  have hupper : 0 < L ^ 2 - 1 := by nlinarith only [hL]
  have hinvpos : 0 < L⁻¹ := inv_pos.mpr hLpos
  have hinvlt : L⁻¹ < 1 := (inv_lt_one₀ hLpos).mpr hL
  have hlower : 0 < 1 - L⁻¹ ^ 2 := by nlinarith only [hinvpos, hinvlt]
  let eta0 := min (min etaA etaE) (min etaB (min (L ^ 2 - 1) (1 - L⁻¹ ^ 2)))
  let delta := min (min deltaA deltaE) (min deltaB deltaM)
  refine ⟨eta0, delta, lt_min (lt_min hetaA hetaE)
    (lt_min hetaB (lt_min hupper hlower)),
    lt_min (lt_min hdeltaA hdeltaE) (lt_min hdeltaB hdeltaM), ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta heta0 comparison hh s hs hst hnear
  have hetaA' : eta ≤ etaA := heta0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hetaE' : eta ≤ etaE := heta0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hetaB' : eta ≤ etaB := heta0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaU : eta ≤ L ^ 2 - 1 :=
    heta0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hetaL : eta ≤ 1 - L⁻¹ ^ 2 :=
    heta0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hnearA : |s - v| < deltaA :=
    hnear.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hnearE : |s - v| < deltaE :=
    hnear.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hnearB : |s - v| < deltaB :=
    hnear.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hnearM : |s - v| < deltaM :=
    hnear.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Eend, heEnd, _, hDEnd, hcEnd, _, _, hiEnd, hrEnd⟩ :=
    hneckE F hinitial S hS t hT hn i J U e initial eta heta hetaE' comparison hh s hs hst hnearE
  obtain ⟨Eboundary, heBoundary, _, hDBoundary, hcBoundary, hsBoundary, _, _, _⟩ :=
    hneckB F hinitial S hS t hT hn i J U e initial eta heta hetaB' comparison hh s hs hst hnearB
  have hAnalytic := hanalytic F hinitial S hS t hT hn i J U e initial eta heta hetaA'
    comparison hh s hs hst v hv hnearA
  have hstime : s ∈ Icc 0 theta := ⟨(comparison.choose_spec.2.2.1 s hs).1, hst⟩
  let q := actualCapSliceChart e initial comparison s hs
  let Q := (F.parameters.h t)⁻¹ ^ 2
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr hh)
  let g' := m01RescaledMetric (F.metric (t + s / Q)) Q hQ
  let D' := m01RescaledMetric_connection (F.metric (t + s / Q))
    (F.connection (t + s / Q)) Q hQ
  let Eend' : EpsilonNeck g' := Eend.scaleMetric Q hQ
  let Eboundary' : EpsilonNeck g' := Eboundary.scaleMetric Q hQ
  let : CompactSpace (F.slice (t + s / Q)).carrier :=
    isCompact_univ_iff.mp (F.slices_compact _ (e.time_subset ⟨s, hs, rfl⟩))
  have hqsource : q.source = F.standard_initial.metric.ball 0 A :=
    actualCapSliceChart_source e initial comparison s hs
  have hDEnd' : Eend'.connection = D' :=
    congrArg (fun D => M13.scaleLeviCivitaData D Q hQ) hDEnd
  have hDBoundary' : Eboundary'.connection = D' :=
    congrArg (fun D => M13.scaleLeviCivitaData D Q hQ) hDBoundary
  have hregions : Eend'.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) =
      q '' N.end_neck.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) :=
    hrEnd _ _ (by rw [N.end_neck_epsilon]) (by
      rw [N.end_neck_epsilon]
      have h := inv_pos.mpr N.epsilon_pos
      linarith)
  cases hinitial
  cases hS
  have hcompare (x : StandardCapSpace) (hx : x ∈ N.carrier) :
      |D'.scalarCurvature (q x) - N.connection.scalarCurvature x| ≤ nu ∧
      |scalarGradientNorm g' D' (q x) - scalarGradientNorm (standard.flow.metric v)
        N.connection x| ≤ nu ∧
      |(D'.laplacian D'.scalarCurvature (q x) + 2 * D'.ricciNormSq (q x)) -
        (N.connection.laplacian N.connection.scalarCurvature x +
          2 * N.connection.ricciNormSq x)| ≤ nu := by
    have htuple : ‖(D'.scalarCurvature (q x), scalarGradientNorm g' D' (q x),
        D'.laplacian D'.scalarCurvature (q x) + 2 * D'.ricciNormSq (q x)) -
        (N.connection.scalarCurvature x,
          scalarGradientNorm (standard.flow.metric v) N.connection x,
          N.connection.laplacian N.connection.scalarCurvature x +
            2 * N.connection.ricciNormSq x)‖ ≤ nu := by
      rw [hconnection,
        capComparison_scaled_analytic_readout e initial comparison hh s hs (hsource hx)]
      exact hAnalytic x (hsource hx)
    exact ⟨(norm_fst_le _).trans htuple, (norm_fst_le _).trans ((norm_snd_le _).trans htuple),
      (norm_snd_le _).trans ((norm_snd_le _).trans htuple)⟩
  have htangent (x : StandardCapSpace) (hx : x ∈ q.source)
      (w : TangentSpace (𝓡 3) x) :
      g'.tangentNorm (q x) (mfderiv (𝓡 3) (𝓡 3) q x w) ≤
          Lambda * (standard.flow.metric v).tangentNorm x w ∧
        (standard.flow.metric v).tangentNorm x w ≤
          Lambda * g'.tangentNorm (q x) (mfderiv (𝓡 3) (𝓡 3) q x w) := by
    have hphysical := actualCapSliceChart_tangent_bounds e initial comparison hh heta hLpos
      hetaU hetaL s hs (hqsource ▸ hx) w
    have htime := hmetricTime s hstime v hv hnearM x w
    constructor
    · calc
        _ ≤ L * (standard.flow.metric s).tangentNorm x w := hphysical.1
        _ ≤ L * (L * (standard.flow.metric v).tangentNorm x w) :=
          mul_le_mul_of_nonneg_left htime.1 hLpos.le
        _ = _ := by rw [← mul_assoc, hLsq]
    · calc
        _ ≤ L * (standard.flow.metric s).tangentNorm x w := htime.2
        _ ≤ L * (L * g'.tangentNorm (q x) (mfderiv (𝓡 3) (𝓡 3) q x w)) :=
          mul_le_mul_of_nonneg_left hphysical.2 hLpos.le
        _ = _ := by rw [← mul_assoc, hLsq]
  obtain ⟨H, hHe, hHC, _, hHcore, _, hHcarrier, _, _, _, _⟩ :=
    hcap g' D' q.toOpenPartialHomeomorph q.contMDiffOn_toFun q.contMDiffOn_invFun
      (by change N.carrier ⊆ q.source; rw [hqsource]; exact hsource)
      (fun x hx w => (htangent x hx w).1) (fun x hx w => (htangent x hx w).2)
      hcompare Eend' Eboundary' (heEnd.trans N.end_neck_epsilon)
      (heBoundary.trans N.boundary_neck_epsilon) hDEnd' hDBoundary' hcEnd hcBoundary
      (by rw [N.boundary_eq_neck_sphere]; exact hsBoundary) hiEnd hregions
  obtain ⟨K, hKe, hKC, hKD, hKcore, hKcarrier⟩ :=
    exists_cap_of_rescaled_metric (F.metric (t + s / Q)) (F.connection (t + s / Q)) hQ H
  exact ⟨K, hKe.trans hHe, hKC.trans hHC, hKD, hKcore.trans hHcore, hKcarrier.trans hHcarrier⟩

end PoincareConjecture.Proofs.M47
