import PoincareConjecture.Proofs.M32.Claim11_34.SliceBallCoverage
import PoincareConjecture.Proofs.M32.Claim11_35.CapNormalizedBounds
import PoincareConjecture.Proofs.M04.ScalarEvolution














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space




theorem blowup_eventually_caps_contained_on_slice
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    (hpositive : ∀ x ∈ K, 0 < (G.limit.flow.connection t).scalarCurvature x)
    {B : ℝ} (hB : 0 < B) :
    ∃ Kplus : Set G.limit.carrier.carrier, IsCompact Kplus ∧ K ⊆ Kplus ∧
      ∃ Lambda : ℝ, 0 < Lambda ∧
        ∀ᶠ k in atTop, ∃ htk : t ∈ Icc (-G.exhaustion.time k) 0,
          Kplus ⊆ (blowup_sliceEmbedding G k t htk).source ∧
          ∀ x ∈ K, ∀ C : CapCertificate ((S.flow (G.subsequence k)).metric
              ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))),
            C.cap_constant ≤ B →
            C.connection = (S.flow (G.subsequence k)).connection
              ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)) →
            blowup_sliceEmbedding G k t htk x ∈ C.core →
            C.carrier ⊆ (blowup_sliceEmbedding G k t htk).target ∧
              (blowup_sliceEmbedding G k t htk).symm '' C.carrier ⊆ Kplus ∧
              S.scale (G.subsequence k) * C.boundary_neck.scale ^ 2 ≤ Lambda := by
  have hf : ContinuousOn (G.limit.flow.connection t).scalarCurvature K :=
    (G.limit.flow.contMDiff_scalarCurvature t ht).continuous.continuousOn
  obtain ⟨b, hb, hbound⟩ := hK.exists_forall_le' hf hpositive
  let m := b / 2
  have hm : 0 < m := by dsimp [m]; positivity
  let r := B * m ^ (-1 / 2 : ℝ)
  have hr : 0 < r := mul_pos hB (Real.rpow_pos_of_pos hm _)
  obtain ⟨Kplus, hplus, hKK, hcover⟩ := blowup_eventually_slice_inverse_balls G ht hK hr
  refine ⟨Kplus, hplus, hKK, B / m, div_pos hB hm, ?_⟩
  filter_upwards [hcover, blowup_eventually_sliceScalar_error G ht hK hm] with k hc hs
  obtain ⟨htk, hsource, hballs⟩ := hc
  obtain ⟨htk', _, hscalar⟩ := hs
  refine ⟨htk, hsource, ?_⟩
  intro x hx C hCB hconnection hcore
  have hcarrier : blowup_sliceEmbedding G k t htk x ∈ C.carrier := by
    rw [C.core_eq_interior_closed_core] at hcore
    have hclosed := interior_subset hcore
    rw [C.closed_core_eq_complement_end] at hclosed
    exact hclosed.1
  have hnormalized : m ≤ C.connection.scalarCurvature
      (blowup_sliceEmbedding G k t htk x) / S.scale (G.subsequence k) := by
    rw [hconnection]
    have h := hscalar x hx
    change |((S.flow (G.subsequence k)).connection
      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).scalarCurvature
      (blowup_sliceEmbedding G k t htk x) / S.scale (G.subsequence k) -
      (G.limit.flow.connection t).scalarCurvature x| < m at h
    have hb' : b = 2 * m := by dsimp [m]; ring
    linarith [(abs_lt.mp h).1, hbound x hx]
  obtain ⟨hcapball, hscale⟩ := cap_normalized_carrier_and_boundary_scale C
    (S.base_scalar_pos (G.subsequence k)) hm hCB hcarrier hnormalized
  refine ⟨fun y hy => ((hballs x hx).2 y (hcapball hy)).1, ?_, hscale⟩
  rintro y ⟨z, hz, rfl⟩
  exact ((hballs x hx).2 z (hcapball hz)).2

end PoincareConjecture.M32
