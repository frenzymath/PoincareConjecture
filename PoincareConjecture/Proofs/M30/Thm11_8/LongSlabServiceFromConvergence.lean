import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSourcePrefix
import PoincareConjecture.Proofs.M30.Thm11_8.LongSlabService
import PoincareConjecture.Proofs.M30.Generalized.BlowupSubsequence
import PoincareConjecture.Proofs.M30.Thm5_33.CurvatureNorm














set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold



theorem longSlabControlService_of_convergence
    (hC : RicciFlowCurvatureTheory.{u})
    {S : GeneralizedBlowupSequence.{u}} {T0 : ℝ≥0∞}
    {epsilon C kappa r0 mu : ℝ}
    (H : M30LongBlowupControls S epsilon C kappa r0 mu T0)
    (G : GeneralizedBlowupConvergence S (blowupBackwardInterval T0)) :
    M30LongSlabControlService
      (reindexedBlowupSequence S G.subsequence G.subsequence_strictMono) kappa r0 T0 := by
  let S' := reindexedBlowupSequence S G.subsequence G.subsequence_strictMono
  refine { bounds := ?_ }
  intro T hT hTT0
  have hI : Icc (-T) 0 ⊆ blowupBackwardInterval T0 :=
    closedSlab_subset_blowupBackwardInterval hTT0
  obtain ⟨K, _hK, hKbound⟩ :=
    G.limit.curvature_locally_bounded_in_time (Icc (-T) 0) isCompact_Icc hI
  have hscalar : ∀ s ∈ Icc (-T) 0, ∀ x,
      (G.limit.flow.connection s).scalarCurvature x ≤ 9 * K := by
    intro s hs x
    have habs := (G.limit.flow.connection s).abs_scalarCurvature_le_curvatureTensorNorm x
    norm_num only [Nat.cast_ofNat, sq] at habs
    have hnorm := (le_abs_self _).trans (hKbound s hs x)
    have hle := (le_abs_self _).trans habs
    nlinarith
  let D : ℝ := max 4 (9 * K + 1)
  have hD : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _)
  have hmax : max D 1 = D :=
    max_eq_left ((by norm_num : (1 : ℝ) ≤ 4).trans (le_max_left _ _))
  obtain ⟨Tplus, _hTplusNonneg, hTTplus, hTplusT0⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp hTT0
  have hTplus : 0 < Tplus := ENNReal.ofReal_pos.mp
    ((ENNReal.ofReal_pos.mpr hT).trans hTTplus)
  have hTTplus' : T < Tplus :=
    (ENNReal.ofReal_lt_ofReal_iff hTplus).mp hTTplus
  refine ⟨13 * D, mul_nonneg (by norm_num) hD, ?_⟩
  intro A hA eta heta
  have hprefix := eventually_finiteSlab_scalar_of_generalized_limit_bound_on_prefix
    G hA (H.slabs Tplus hTplus hTplusT0 A hA) T hT hTTplus' hI
    (fun s hs x _hx => hscalar s hs x)
  have hpinch := G.subsequence_strictMono.tendsto_atTop.eventually
    (eventually_curvatureNorm_and_negativeDefect_le hC S H.branch D hD eta heta)
  filter_upwards [hprefix, hpinch] with k hk hpinchK
  obtain ⟨e, he⟩ := hk
  let e' : M30FiniteHorizonSlab S' k A Tplus kappa r0 := {
    embedding := e.embedding
    zero_identity := e.zero_identity
    noncollapsed := e.noncollapsed }
  refine ⟨Tplus, hTplus, hTTplus', hTplusT0, e', ?_, ?_⟩
  · intro s hs x hx
    let p := (FiniteHorizonSlab.closedEmbedding e hTTplus').pointMap s hs x
    have hp : p.1 ∈ (S.flow (G.subsequence k)).interval :=
      ((S.flow (G.subsequence k)).slice_nonempty_iff p.1).mp ⟨p.2⟩
    have h := (hpinchK p.1 hp p.2 (he s hs x hx)).1
    rw [hmax] at h
    exact h
  · intro s hs x hx
    let p := (FiniteHorizonSlab.closedEmbedding e hTTplus').pointMap s hs x
    have hp : p.1 ∈ (S.flow (G.subsequence k)).interval :=
      ((S.flow (G.subsequence k)).slice_nonempty_iff p.1).mp ⟨p.2⟩
    exact (hpinchK p.1 hp p.2 (he s hs x hx)).2

end PoincareConjecture.M30
