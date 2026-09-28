import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedCompactImages
import PoincareConjecture.Proofs.M30.Thm11_8.LongSlabService
import PoincareConjecture.Proofs.M30.Thm11_8.HorizonTimeSequence
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardInterval











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold




theorem eventually_generalized_point_noncollapsed_of_longSlabService
    {S : GeneralizedBlowupSequence.{u}} {T0 : ℝ≥0∞} {kappa r0 : ℝ}
    (G : GeneralizedBlowupConvergence S (blowupBackwardInterval T0))
    (H : M30LongSlabControlService S kappa r0 T0)
    {t : ℝ} (ht : t ∈ blowupBackwardInterval T0)
    (p : G.limit.carrier.carrier) :
    ∀ᶠ k in atTop, ∀ htk : t ∈ Icc (-G.exhaustion.time k) 0,
      GeneralizedKappaNoncollapsedAt (S.flow (G.subsequence k))
        ((G.embedding k).pointMap t htk p) kappa r0 := by
  have hT0 : 0 < T0 := zero_mem_blowupBackwardInterval.mp G.limit.zero_mem
  obtain ⟨T, _hmono, hT, _hcofinal, hcover⟩ :=
    exists_strictMono_backward_time_exhaustion hT0
  obtain ⟨j, hj⟩ := (hcover {t} isCompact_singleton (singleton_subset_iff.mpr ht)).exists
  have htT : t ∈ Icc (-T j) 0 := hj (mem_singleton t)
  obtain ⟨R, hR, hRtail⟩ :=
    exists_eventually_generalized_terminal_image_baseBall G (K := {p}) isCompact_singleton
  obtain ⟨i, hi⟩ := exists_generalized_exhaustion_stage G (K := {p}) isCompact_singleton
  obtain ⟨B, _hB, hfamily⟩ := H.noncollapsedBounds (T j) (hT j).1 (hT j).2
  have hfamily' := G.subsequence_strictMono.tendsto_atTop.eventually
    (hfamily R hR 1 zero_lt_one)
  filter_upwards [hRtail, eventually_ge_atTop i, hfamily'] with k hk hik hEk htk
  obtain ⟨y, hy, hzero⟩ := hk p (mem_singleton p)
  obtain ⟨_Tplus, _hTplus, _hTT, _hTT0, ⟨E⟩⟩ := hEk
  have hp : p ∈ G.exhaustion.space k :=
    G.exhaustion.space_increasing hik (hi (mem_singleton p))
  have h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have h0T : (0 : ℝ) ∈ Icc (-T j) 0 :=
    ⟨neg_nonpos.mpr (hT j).1.le, le_rfl⟩
  have hmeet : (G.embedding k).pointMap 0 h0 p = E.embedding.pointMap 0 h0T y :=
    (hzero h0).trans (E.zero_identity h0T y hy).symm
  have hpoint := Cylinder.pointMap_eq_on_overlap (G.embedding k) E.embedding
    ordConnected_Icc ordConnected_Icc hp hy h0 h0T hmeet t htk htT
  rw [hpoint]
  exact E.noncollapsed t htT y hy

end PoincareConjecture.M30
