import PoincareConjecture.Proofs.M30.Generalized.CylinderSpatialHomeomorph
import PoincareConjecture.Proofs.M13.Metric

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

noncomputable def normalizedBlowupSliceMetric (S : GeneralizedBlowupSequence.{u})
    (k : ℕ) (t : ℝ) :
    RiemannianMetric 3
      ((S.flow k).slice ((S.base k).1 + t / S.scale k)).carrier :=
  M13.scaleSmoothMetric ((S.flow k).metric ((S.base k).1 + t / S.scale k))
    (S.scale k) (S.base_scalar_pos k)

noncomputable def generalizedSliceHomeomorph
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (-G.exhaustion.time k) 0) :
    OpenPartialHomeomorph G.limit.carrier.carrier
      ((S.flow (G.subsequence k)).slice
        ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).carrier := by
  let W : SpacetimeInterval := {
    domain := Icc (-G.exhaustion.time k) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-G.exhaustion.time k,
      ⟨le_rfl, neg_nonpos.mpr (G.exhaustion.time_pos k).le⟩,
      0, ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩,
      (neg_lt_zero.mpr (G.exhaustion.time_pos k)).ne⟩ }
  let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
    ⟨G.exhaustion.space k, G.exhaustion.space_open k⟩
  exact Cylinder.spatialHomeomorph (J := W) (U := U) (G.embedding k) ⟨t, ht⟩

theorem generalizedSliceHomeomorph_contMDiffAt
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (-G.exhaustion.time k) 0) {x : G.limit.carrier.carrier}
    (hx : x ∈ G.exhaustion.space k) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (generalizedSliceHomeomorph G k t ht) x :=
  (G.embedding k).forward_smooth t ht x hx |>.contMDiffAt
    ((G.exhaustion.space_open k).mem_nhds hx)

theorem generalizedSliceHomeomorph_symm_contMDiffAt
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (-G.exhaustion.time k) 0)
    {y : ((S.flow (G.subsequence k)).slice
      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).carrier}
    (hy : y ∈ (generalizedSliceHomeomorph G k t ht).target) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (generalizedSliceHomeomorph G k t ht).symm y :=
  ((G.embedding k).inverse_smooth t ht y hy).contMDiffAt
    ((generalizedSliceHomeomorph G k t ht).open_target.mem_nhds hy)

theorem exists_generalized_exhaustion_stage
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {K : Set G.limit.carrier.carrier}
    (hK : IsCompact K) : ∃ j, K ⊆ G.exhaustion.space j := by
  exact hK.elim_directed_cover G.exhaustion.space G.exhaustion.space_open
    (by
      change K ⊆ (⋃ j, G.exhaustion.space j : Set G.limit.sliceCarrier.carrier)
      rw [G.exhaustion.space_covers]
      exact subset_univ _)
    G.exhaustion.space_increasing.directed_le

theorem exists_generalized_time_shift
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J) :
    ∃ N : ℕ, ∀ k : ℕ, t ∈ Icc (-G.exhaustion.time (k + N)) 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (G.exhaustion.time_cofinal {t} isCompact_singleton (singleton_subset_iff.mpr ht))
  exact ⟨N, fun k => hN (k + N) (by omega) (mem_singleton t)⟩

end PoincareConjecture.M30
