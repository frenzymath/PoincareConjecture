import PoincareConjecture.Proofs.M47.BlowupControlsCapImageCertificate
import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckImage
import PoincareConjecture.Proofs.M47.BlowupControlsCapTangent
import PoincareConjecture.Proofs.M47.BlowupControlsCapScaling
import PoincareConjecture.Proofs.M04.PointwiseFlatness











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47




theorem exists_actualCap_physical_certificate_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A v : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (hv : v ∈ Icc 0 theta)
    (N : CapCertificate (standard.flow.metric v))
    (hconnection : N.connection = standard.flow.connection v)
    (hsource : N.carrier ⊆ g0.metric.ball 0 A) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (hs : v ∈ J),
      let q := actualCapSliceChart e initial comparison v hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      ∃ H : CapCertificate (F.metric (t + v / Q)),
        H.epsilon = N.epsilon ∧ H.cap_constant = N.cap_constant ∧
        H.connection = F.connection (t + v / Q) ∧
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
  obtain ⟨etaA, hetaA, hanalytic⟩ :=
    exists_actualCap_analytic_comparison_tolerance standard htheta hA hnu
  obtain ⟨etaE, hetaE, hneckE⟩ := exists_actualCap_image_neck_tolerance standard htheta hA
    hv.2 N.end_neck (N.end_neck_connection.trans hconnection) (N.end_neck_subset.trans hsource)
  obtain ⟨etaB, hetaB, hneckB⟩ := exists_actualCap_image_neck_tolerance standard htheta hA
    hv.2 N.boundary_neck (N.boundary_neck_connection.trans hconnection)
    (N.boundary_neck_subset.trans hsource)
  have hLpos : 0 < Lambda := zero_lt_one.trans hLambda
  have hupper : 0 < Lambda ^ 2 - 1 := by nlinarith
  have hinvpos : 0 < Lambda⁻¹ := inv_pos.mpr hLpos
  have hinvlt : Lambda⁻¹ < 1 := (inv_lt_one₀ hLpos).mpr hLambda
  have hlower : 0 < 1 - Lambda⁻¹ ^ 2 := by nlinarith
  let eta0 := min (min etaA etaE) (min etaB (min (Lambda ^ 2 - 1) (1 - Lambda⁻¹ ^ 2)))
  refine ⟨eta0, lt_min (lt_min hetaA hetaE) (lt_min hetaB (lt_min hupper hlower)), ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta heta0 comparison hh hs
  have hetaA' : eta ≤ etaA := heta0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hetaE' : eta ≤ etaE := heta0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hetaB' : eta ≤ etaB := heta0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaU : eta ≤ Lambda ^ 2 - 1 :=
    heta0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hetaL : eta ≤ 1 - Lambda⁻¹ ^ 2 :=
    heta0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨Eend, heEnd, _, hDEnd, hcEnd, _, _, hiEnd, hrEnd⟩ :=
    hneckE F hinitial S hS t hT hn i J U e initial eta heta hetaE' comparison hh hs
  obtain ⟨Eboundary, heBoundary, _, hDBoundary, hcBoundary, hsBoundary, _, _, _⟩ :=
    hneckB F hinitial S hS t hT hn i J U e initial eta heta hetaB' comparison hh hs
  have hAnalytic := hanalytic F hinitial S hS t hT hn i J U e initial eta heta hetaA'
    comparison hh v hs hv.2
  let q := actualCapSliceChart e initial comparison v hs
  let Q := (F.parameters.h t)⁻¹ ^ 2
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr hh)
  let g' := m01RescaledMetric (F.metric (t + v / Q)) Q hQ
  let D' := m01RescaledMetric_connection (F.metric (t + v / Q))
    (F.connection (t + v / Q)) Q hQ
  let Eend' : EpsilonNeck g' := Eend.scaleMetric Q hQ
  let Eboundary' : EpsilonNeck g' := Eboundary.scaleMetric Q hQ
  let : CompactSpace (F.slice (t + v / Q)).carrier :=
    isCompact_univ_iff.mp (F.slices_compact _ (e.time_subset ⟨v, hs, rfl⟩))
  have hqsource : q.source = F.standard_initial.metric.ball 0 A :=
    actualCapSliceChart_source e initial comparison v hs
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
        capComparison_scaled_analytic_readout e initial comparison hh v hs (hsource hx)]
      exact hAnalytic x (hsource hx)
    exact ⟨(norm_fst_le _).trans htuple, (norm_fst_le _).trans ((norm_snd_le _).trans htuple),
      (norm_snd_le _).trans ((norm_snd_le _).trans htuple)⟩
  obtain ⟨H, hHe, hHC, _, hHcore, _, hHcarrier, _, _, _, _⟩ :=
    hcap g' D' q.toOpenPartialHomeomorph q.contMDiffOn_toFun q.contMDiffOn_invFun
      (by change N.carrier ⊆ q.source; rw [hqsource]; exact hsource)
      (fun x hx w => (actualCapSliceChart_tangent_bounds e initial comparison hh heta hLpos
        hetaU hetaL v hs (hqsource ▸ hx) w).1)
      (fun x hx w => (actualCapSliceChart_tangent_bounds e initial comparison hh heta hLpos
        hetaU hetaL v hs (hqsource ▸ hx) w).2)
      hcompare Eend' Eboundary' (heEnd.trans N.end_neck_epsilon)
      (heBoundary.trans N.boundary_neck_epsilon) hDEnd' hDBoundary' hcEnd hcBoundary
      (by rw [N.boundary_eq_neck_sphere]; exact hsBoundary) hiEnd hregions
  obtain ⟨K, hKe, hKC, hKD, hKcore, hKcarrier⟩ :=
    exists_cap_of_rescaled_metric (F.metric (t + v / Q)) (F.connection (t + v / Q)) hQ H
  exact ⟨K, hKe.trans hHe, hKC.trans hHC, hKD, hKcore.trans hHcore, hKcarrier.trans hHcarrier⟩

end PoincareConjecture.M47
