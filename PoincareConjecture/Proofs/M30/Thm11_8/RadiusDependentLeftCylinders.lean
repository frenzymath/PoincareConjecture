import PoincareConjecture.Statements.M30Providers
import PoincareConjecture.Proofs.M30.Generalized.BlowupSubsequence
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteCompactScalarBound
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSourcePrefix
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSlabContinuation
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSlabControlled










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space






theorem exists_radius_dependent_left_cylinders_threshold
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ (S : GeneralizedBlowupSequence.{u})
        (epsilon C kappa r0 mu : ℝ),
        epsilon ≤ epsilon0 →
      ∀ _H : M30CommonBlowupControls S epsilon C kappa r0 mu,
      ∀ (T Tplus : ℝ), 0 < T → T < Tplus →
      ∀ G : GeneralizedBlowupConvergence S (Ioc (-T) 0),
        (∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
          Nonempty (M30FiniteHorizonSlab S k A Tplus kappa r0)) →
      ∀ A : ℝ, 0 < A →
        ∃ delta : ℝ, 0 < delta ∧ T + delta < Tplus ∧
          ∃ B : ℝ, 0 ≤ B ∧
            ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
              Nonempty (NoncollapsedControlledBlowupCylinder S
                (G.subsequence k) A (T + delta) B eta kappa r0) := by
  obtain ⟨epsilon0, hepsilon0, hepsilonMax, hscalarThreshold⟩ :=
    exists_finite_limit_compact_scalar_bound_threshold P
  refine ⟨epsilon0, hepsilon0, hepsilonMax, ?_⟩
  intro S epsilon C kappa r0 mu hepsilonLe _H T Tplus hT hTTplus G hslabs A hA
  have hHyp : GeneralizedBoundedDistanceHypotheses S epsilon C :=
    ⟨_H.branch, _H.canonical⟩
  obtain ⟨B0, hB0, hscalar⟩ := hscalarThreshold S epsilon C _H.epsilon_pos
    hepsilonLe _H.C_pos hHyp T hT G (2 * A) (by linarith)
  let D : ℝ := max 4 (B0 + 1)
  have hD : 4 ≤ D := by
    exact le_max_left _ _
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  let S' : GeneralizedBlowupSequence :=
    reindexedBlowupSequence S G.subsequence G.subsequence_strictMono
  let G' : GeneralizedBlowupConvergence S' (Ioc (-T) 0) := {
    limit := G.limit
    subsequence := id
    subsequence_strictMono := strictMono_id
    exhaustion := G.exhaustion
    embedding := G.embedding
    base_preserving := G.base_preserving
    source_balls_in_image := G.source_balls_in_image
    pullback_metric_CInfinity := G.pullback_metric_CInfinity }
  let H' : M30CommonBlowupControls S' epsilon C kappa r0 mu :=
    reindexedCommonBlowupControls _H G.subsequence G.subsequence_strictMono
  have hslabs' : ∀ᶠ k : ℕ in atTop,
      Nonempty (M30FiniteHorizonSlab S' k A Tplus kappa r0) := by
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually
      (hslabs A hA)] with k hk
    obtain ⟨e⟩ := hk
    refine ⟨{
      embedding := e.embedding
      zero_identity := e.zero_identity
      noncollapsed := e.noncollapsed }⟩
  have hprefix : ∀ t : ℝ, 0 < t → ∀ htT : t < T,
      ∀ᶠ k : ℕ in atTop,
        ∃ e : M30FiniteHorizonSlab S' k A Tplus kappa r0,
          ∀ s (hs : s ∈ Icc (-t) 0)
            (x : ((S'.flow k).slice (S'.base k).1).carrier),
            x ∈ S'.baseBall k A →
              (S'.flow k).scalar
                ((FiniteHorizonSlab.closedEmbedding e
                  (htT.trans hTTplus)).pointMap s hs x) ≤
                D * S'.scale k := by
    intro t ht htT
    have hprefix' := eventually_finiteSlab_prefix_scalar_of_limit_bound
      (S := S') (T := T) G' hA hTTplus hslabs' (by
        simpa only [G', S', reindexedBlowupSequence,
          GeneralizedBlowupSequence.scale, GeneralizedBlowupSequence.baseBall] using hscalar)
        t ht htT
    filter_upwards [hprefix'] with k hk
    obtain ⟨e, he⟩ := hk
    refine ⟨e, ?_⟩
    intro s hs x hx
    simpa only [D, G', S', reindexedBlowupSequence, Function.id_def,
      GeneralizedBlowupSequence.scale, GeneralizedBlowupSequence.baseBall] using he s hs x hx
  obtain ⟨hdelta, hbuffer, hfamily⟩ :=
    eventually_finiteSlab_bounds_of_uniform_prefix_scalar
      P.m04 H' A T Tplus D hA hT hTTplus hD hprefix
  refine ⟨_, hdelta, hbuffer, 26 * D, ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (le_trans (by norm_num) hD)
  · intro eta heta
    filter_upwards [hfamily eta heta] with k hk
    obtain ⟨e, hcurv, hdefect⟩ := hk
    refine ⟨by
      let e' := noncollapsedControlledCylinderOfFiniteHorizonSlab e hbuffer
        (fun s hs x _hx => hcurv s hs x)
        (fun s hs x _hx => hdefect s hs x)
      exact {
        embedding := e'.embedding
        zero_identity := e'.zero_identity
        curvature_bound := e'.curvature_bound
        negative_curvature_bound := e'.negative_curvature_bound
        noncollapsed := e'.noncollapsed }
      ⟩

end PoincareConjecture.M30
