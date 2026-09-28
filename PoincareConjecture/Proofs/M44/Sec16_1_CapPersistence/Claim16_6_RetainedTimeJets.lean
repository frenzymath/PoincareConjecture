import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedBilinearLimit
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RicciTimeGluing
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_ClosedTimeJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance retainedTimeBilinearNorm : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance retainedTimeBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T b : ℝ}




noncomputable def retainedChartCoefficients
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b))
    (q : (slice event.tMinus).carrier) (p : ℝ × E) : Bilin :=
  if p.1 < T then
    (event.pre_flow.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm p.2
  else
    (G.metric p.1).pullbackCoefficients
      (event.retention.map ∘ (extChartAt (𝓡 3) q).symm) p.2




theorem retained_inverse_coordinates_smooth
    (event : SurgeryEventData g0 K P slice metric T)
    (q : (slice event.tMinus).carrier) {U : Set E}
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (event.retention.map ∘ (extChartAt (𝓡 3) q).symm) U :=
  (event.retention.map_smooth.mono interior_subset).comp
    ((contMDiffOn_extChartAt_symm q).mono hchart)
    (fun _x hx => hret (mem_image_of_mem _ hx))



theorem retainedChartCoefficients_smooth_before
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b))
    (q : (slice event.tMinus).carrier) {U : Set E} (hU : IsOpen U)
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target) :
    ContDiffOn ℝ ∞ (retainedChartCoefficients event G q) (Ioo event.tMinus T ×ˢ U) := by
  have hs := (contDiffOn_pullbackCoefficients_within event.pre_flow hU
    ((contMDiffOn_extChartAt_symm q).mono hchart)).mono
      (prod_mono Ioo_subset_Ico_self Subset.rfl)
  apply hs.congr
  intro p hp
  simp only [retainedChartCoefficients, if_pos hp.1.2]




theorem retainedChartCoefficients_smooth_after
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b))
    (q : (slice event.tMinus).carrier) {U : Set E} (hU : IsOpen U)
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre) :
    ContDiffOn ℝ ∞ (retainedChartCoefficients event G q) (Ico T b ×ˢ U) := by
  have hs := (contDiffOn_pullbackCoefficients_within G hU
    (retained_inverse_coordinates_smooth event q hchart hret)).mono
      (prod_mono Ico_subset_Icc_self Subset.rfl)
  apply hs.congr
  intro p hp
  simp only [retainedChartCoefficients, if_neg (not_lt_of_ge hp.1.1)]




theorem retainedChartCoefficients_continuous_spatialJets
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b)) (hTb : T < b)
    (hbirth : G.metric T = metric T)
    (q : (slice event.tMinus).carrier) (hq : q ∈ interior event.retained_pre)
    {U : Set E} (hU : IsOpen U) (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre) :
    ∀ m : ℕ, ContinuousOn (fun p : ℝ × E =>
      iteratedFDeriv ℝ m (fun x => retainedChartCoefficients event G q (p.1, x)) p.2)
      (Ioo event.tMinus b ×ˢ U) := by
  apply continuousOn_spatialJets_of_compact_uniform hU hTb
    (retainedChartCoefficients_smooth_before event G q hU hchart)
    (retainedChartCoefficients_smooth_after event G q hU hchart hret)
  intro m L hL hLU eta heta
  obtain ⟨d, hd, hbound⟩ := retained_bilinear_jet_limit event q hq hU hchart hret
    m hL hLU heta
  refine ⟨d, hd, ?_⟩
  intro t ht hT x hx
  simpa only [retainedChartCoefficients, if_pos hT, lt_self_iff_false, if_false, hbirth]
    using hbound t ht hT x hx




theorem retainedChartCoefficients_spatial_smooth
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b))
    (q : (slice event.tMinus).carrier) {U : Set E} (hU : IsOpen U)
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun x => retainedChartCoefficients event G q (t, x)) U := by
  by_cases ht : t < T
  · simpa only [retainedChartCoefficients, if_pos ht] using
      ((event.pre_flow.metric t).contDiffOn_chartCoefficients q).mono hchart
  · simp only [retainedChartCoefficients, if_neg ht]
    intro x hx
    exact ((G.metric t).contDiffAt_pullbackCoefficients
      ((retained_inverse_coordinates_smooth event q hchart hret).contMDiffAt
        (hU.mem_nhds hx))).contDiffWithinAt

end PoincareConjecture.M44
