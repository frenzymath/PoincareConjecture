import PoincareConjecture.Proofs.M47.BlowupControlsCapImageGeometry
import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticComparison
import PoincareConjecture.Proofs.M47.BlowupControlsCapTangent









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M47

local notation "E" => StandardCapSpace




theorem exists_actualCap_image_geometric_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A v : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (hvtheta : v ≤ theta)
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
        (hh : 0 < F.parameters.h t) (hs : v ∈ J),
      let q := actualCapSliceChart e initial comparison v hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      let hQ := sq_pos_of_pos (inv_pos.mpr hh)
      let g' := m01RescaledMetric (F.metric (t + v / Q)) Q hQ
      let D' := m01RescaledMetric_connection (F.metric (t + v / Q))
        (F.connection (t + v / Q)) Q hQ
      0 < scalarCurvatureSupOn g' D' (q '' N.carrier) ∧
      intrinsicDiameter g' (q '' N.carrier) <
        ENNReal.ofReal (N.cap_constant *
          scalarCurvatureSupOn g' D' (q '' N.carrier) ^ (-1 / 2 : ℝ)) ∧
      calibratedMetricVolume g' (q '' N.carrier) <
        ENNReal.ofReal N.cap_constant *
          ENNReal.ofReal (scalarCurvatureSupOn g' D' (q '' N.carrier) ^ (-3 / 2 : ℝ)) := by
  obtain ⟨Lambda, hLambda, nu, hnu, hgeometry⟩ := exists_cap_image_geometric_tolerance N
  obtain ⟨etaA, hetaA, hanalytic⟩ :=
    exists_actualCap_analytic_comparison_tolerance standard htheta hA hnu
  have hLpos : 0 < Lambda := zero_lt_one.trans hLambda
  have hupper : 0 < Lambda ^ 2 - 1 := by nlinarith
  have hinvpos : 0 < Lambda⁻¹ := inv_pos.mpr hLpos
  have hinvlt : Lambda⁻¹ < 1 := (inv_lt_one₀ hLpos).mpr hLambda
  have hlower : 0 < 1 - Lambda⁻¹ ^ 2 := by nlinarith
  refine ⟨min etaA (min (Lambda ^ 2 - 1) (1 - Lambda⁻¹ ^ 2)),
    lt_min hetaA (lt_min hupper hlower), ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta heta0 comparison hh hs
  have hetaAnalytic : eta ≤ etaA := heta0.trans (min_le_left _ _)
  have hetaUpper : eta ≤ Lambda ^ 2 - 1 :=
    heta0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaLower : eta ≤ 1 - Lambda⁻¹ ^ 2 :=
    heta0.trans ((min_le_right _ _).trans (min_le_right _ _))
  let q := actualCapSliceChart e initial comparison v hs
  let Q := (F.parameters.h t)⁻¹ ^ 2
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr hh)
  let g' := m01RescaledMetric (F.metric (t + v / Q)) Q hQ
  let D' := m01RescaledMetric_connection (F.metric (t + v / Q))
    (F.connection (t + v / Q)) Q hQ
  change 0 < scalarCurvatureSupOn g' D' (q '' N.carrier) ∧
    intrinsicDiameter g' (q '' N.carrier) < _ ∧ calibratedMetricVolume g' (q '' N.carrier) < _
  have hqsource : q.source = F.standard_initial.metric.ball 0 A :=
    actualCapSliceChart_source e initial comparison v hs
  have htargetScalar (x : E) : D'.scalarCurvature (q x) =
      (F.parameters.h t) ^ 2 * (F.connection (t + v / Q)).scalarCurvature
        (e.forward v hs (initial.chart x)) := by
    have h := M13.homothety_scalarCurvature_eq
      (F.metric (t + v / Q)) g' (Diffeomorph.refl (𝓡 3) (F.slice (t + v / Q)).carrier ∞)
      Q hQ (M44.rescaledMetric_identity_homothety hQ)
      (F.connection (t + v / Q)) D' (q x)
    change D'.scalarCurvature (q x) = (F.connection (t + v / Q)).scalarCurvature (q x) / Q at h
    rw [h]
    simp only [q, actualCapSliceChart_apply, Q, inv_pow, div_inv_eq_mul]
    ring
  have hanalytic' := hanalytic F hinitial S hS t hT hn i J U e initial eta heta
    hetaAnalytic comparison hh v hs hvtheta
  cases hinitial
  cases hS
  apply hgeometry _ g' D' q.toOpenPartialHomeomorph (q.contMDiffOn_toFun.of_le (by simp))
  · change N.carrier ⊆ q.source
    rw [hqsource]
    exact hsource
  · intro x hx w
    have hxball : x ∈ F.standard_initial.metric.ball 0 A := hqsource ▸ hx
    exact (actualCapSliceChart_tangent_bounds e initial comparison hh heta hLpos
      hetaUpper hetaLower v hs hxball w).1
  · intro x hx
    change |D'.scalarCurvature (q x) - N.connection.scalarCurvature x| ≤ nu
    rw [htargetScalar, hconnection]
    exact (norm_fst_le _).trans (hanalytic' x (hsource hx))

end PoincareConjecture.M47
