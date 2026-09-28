import PoincareConjecture.Proofs.M47.BlowupControlsCapSliceMap
import PoincareConjecture.Proofs.M47.BlowupControlsCapPhysicalAnalytics
import PoincareConjecture.Proofs.M34.Standard.CapMetricScaling
import PoincareConjecture.Proofs.M34.Standard.CapIsometry










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem capComparison_scaled_analytic_readout
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
    {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J)
    {x : StandardCapSpace} (hx : x ∈ F.standard_initial.metric.ball 0 A) :
    let Q := (F.parameters.h t)⁻¹ ^ 2
    let hQ := sq_pos_of_pos (inv_pos.mpr hh)
    let g' := m01RescaledMetric (F.metric (t + s / Q)) Q hQ
    let D' := m01RescaledMetric_connection (F.metric (t + s / Q))
      (F.connection (t + s / Q)) Q hQ
    let q := actualCapSliceChart e initial comparison s hs
    (D'.scalarCurvature (q x), scalarGradientNorm g' D' (q x),
      D'.laplacian D'.scalarCurvature (q x) + 2 * D'.ricciNormSq (q x)) =
    ((F.parameters.h t) ^ 2 * (F.connection (t + s / Q)).scalarCurvature (q x),
      (F.parameters.h t) ^ 3 * scalarGradientNorm (F.metric (t + s / Q))
        (F.connection (t + s / Q)) (q x),
      (F.parameters.h t) ^ 4 *
        ((F.connection (t + s / Q)).laplacian
          (F.connection (t + s / Q)).scalarCurvature (q x) +
          2 * (F.connection (t + s / Q)).ricciNormSq (q x))) := by
  let Q := (F.parameters.h t)⁻¹ ^ 2
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr hh)
  let D := F.connection (t + s / Q)
  let q := actualCapSliceChart e initial comparison s hs
  change ((M13.scaleLeviCivitaData D Q hQ).scalarCurvature (q x),
    scalarGradientNorm (M13.scaleSmoothMetric (F.metric (t + s / Q)) Q hQ)
      (M13.scaleLeviCivitaData D Q hQ) (q x),
    (M13.scaleLeviCivitaData D Q hQ).laplacian
      (M13.scaleLeviCivitaData D Q hQ).scalarCurvature (q x) +
      2 * (M13.scaleLeviCivitaData D Q hQ).ricciNormSq (q x)) = _
  rw [M13.scaleLeviCivitaData_scalarCurvature, M13.scaleSmoothMetric_scalarGradientNorm,
    M13.scaleLeviCivitaData_scalarEvolution]
  exact (capComparison_analytic_readout e initial comparison hh s hs hx).symm.trans
    (capComparison_analytic_height_readout e initial comparison hh s hs hx)



theorem exists_cap_of_rescaled_metric
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) {Q : ℝ} (hQ : 0 < Q)
    (N : CapCertificate (m01RescaledMetric g Q hQ)) :
    ∃ H : CapCertificate g, H.epsilon = N.epsilon ∧ H.cap_constant = N.cap_constant ∧
      H.connection = D ∧ H.core = N.core ∧ H.carrier = N.carrier := by
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  let H := N.scaleMetric Q⁻¹ (inv_pos.mpr hQ)
  have hidentity : MetricHomothety
      (M13.scaleSmoothMetric (m01RescaledMetric g Q hQ) Q⁻¹ (inv_pos.mpr hQ)) g
      (Diffeomorph.refl (𝓡 3) M ∞) 1 := by
    intro x v w
    simp only [Diffeomorph.coe_refl, mfderiv_id,
      one_mul, M13.scaleSmoothMetric_inner, m01RescaledMetric_inner]
    field_simp
    rfl
  obtain ⟨K, hE, hC, hD, hcore, hcarrier⟩ := H.exists_isometric_image_cap
    (Diffeomorph.refl (𝓡 3) M ∞) hidentity D
  refine ⟨K, hE, hC, hD, ?_, ?_⟩
  · have hc : K.core = H.core := by
      simpa only [Diffeomorph.coe_refl, image_id] using hcore
    exact hc
  · have hc : K.carrier = H.carrier := by
      simpa only [Diffeomorph.coe_refl, image_id] using hcarrier
    exact hc

end PoincareConjecture.M47
