import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderLocalFlow
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CoordinateFlow










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance cylinderFlowCoefficientNorm :
    NormedAddCommGroup (SpacetimeBounds.MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance cylinderFlowCoefficientSpace :
    NormedSpace ℝ (SpacetimeBounds.MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale B : ℝ} {U : Set C.carrier}

set_option maxHeartbeats 800000 in




theorem cylinderTimeCoefficients_smooth_ricci
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 B) U) (hU : IsOpen U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) (hmap : f.target ⊆ U)
    (r0 : ℝ) (hr0 : r0 ∈ Ico 0 B) :
    ContDiffOn ℝ ∞ (cylinderTimeCoefficients e f r0 hr0)
        (Ico origin (origin + B / scale) ×ˢ f.source) ∧
      ∀ t ∈ Ico origin (origin + B / scale), ∀ x ∈ f.source,
        HasDerivWithinAt (fun s => cylinderTimeCoefficients e f r0 hr0 (s, x))
          (SpacetimeBounds.ricciFlowOperator 3 (SpacetimeBounds.metricTwoJet
            (fun y => cylinderTimeCoefficients e f r0 hr0 (t, y)) x))
          (Ico origin (origin + B / scale)) t := by
  let J := Ico origin (origin + B / scale)
  have hlocal (t : ℝ) (ht : t ∈ J) :
      ∃ K : Set ℝ, K ∈ 𝓝 t ∧ t ∈ K ∧
        ContDiffOn ℝ ∞ (cylinderTimeCoefficients e f r0 hr0) ((J ∩ K) ×ˢ f.source) ∧
        ∀ s ∈ J ∩ K, ∀ y ∈ f.source,
          HasDerivWithinAt (fun r => cylinderTimeCoefficients e f r0 hr0 (r, y))
            (SpacetimeBounds.ricciFlowOperator 3 (SpacetimeBounds.metricTwoJet
              (fun z => cylinderTimeCoefficients e f r0 hr0 (s, z)) y)) (J ∩ K) s := by
    have hs := (cylinder_parameter_mem_ico e B t).mpr ht
    simpa only [cylinder_clock_parameter e] using
      cylinderTimeCoefficients_local_smooth_ricci P hpinch e hU f hmap r0 hr0 _ hs
  refine ⟨?_, ?_⟩
  · rintro ⟨t, x⟩ ⟨ht, hx⟩
    obtain ⟨K, hK, htK, hsmooth, _⟩ := hlocal t ht
    apply (hsmooth (t, x) ⟨⟨ht, htK⟩, hx⟩).mono_of_mem_nhdsWithin
    have hKn : {p : ℝ × E | p.1 ∈ K} ∈ 𝓝 (t, x) :=
      continuous_fst.continuousAt.preimage_mem_nhds hK
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hKn] with p hp hpK
    exact ⟨⟨hp.1, hpK⟩, hp.2⟩
  · intro t ht x hx
    obtain ⟨K, hK, htK, _, hevol⟩ := hlocal t ht
    apply (hasDerivWithinAt_inter hK).mp
    exact hevol t ⟨ht, htK⟩ x hx





theorem exists_cylinder_coordinate_flow
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 B) U) (hU : IsOpen U) (hB : 0 < B)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) (hmap : f.target ⊆ U) :
    ∃ G : RicciFlow 3 (⟨f.source, f.open_source⟩ : Opens E)
        (Ico origin (origin + B / scale)),
      ∀ t, ∀ (x : (⟨f.source, f.open_source⟩ : Opens E))
        (v w : TangentSpace (𝓡 3) x),
        (G.metric t).inner x v w =
          cylinderTimeCoefficients e f 0 ⟨le_rfl, hB⟩ (t, x) v w := by
  have hzero : (0 : ℝ) ∈ Ico 0 B := ⟨le_rfl, hB⟩
  have htime : origin < origin + B / scale := by linarith [div_pos hB e.scale_pos]
  obtain ⟨hsmooth, hevol⟩ := cylinderTimeCoefficients_smooth_ricci P hpinch e hU f hmap 0 hzero
  exact exists_ricciFlow_of_open_coefficients (⟨f.source, f.open_source⟩ : Opens E)
    ordConnected_Ico (Ico_infinite htime).nontrivial (cylinderTimeCoefficients e f 0 hzero)
    (cylinderTimeCoefficients_spatial_smooth e f.open_source f.contMDiffOn
      (fun _ hx => hmap (f.map_source hx)) 0 hzero)
    (fun t x _ v w => cylinderTimeCoefficients_symm e f 0 hzero t x v w)
    (fun t _ hx v hv => cylinderTimeCoefficients_pos e hU f hmap 0 hzero t hx v hv)
    hsmooth hevol

end PoincareConjecture.M44
