import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.BlowupSubsequence
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.FiniteSlab.FiniteSourcePrefix
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data

/-!
# Uniform source prefixes from a finite generalized limit

This adapter isolates the reindexing bookkeeping in Claim 11.17.  A finite
generalized convergence whose limiting scalar is bounded on the whole retained
carrier transfers that bound to every fixed source ball with one coefficient
chosen before the radius.  It is deliberately a finite-window statement: it
does not construct a new convergence or extend the time interval.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

/-- A global scalar bound on one finite generalized limit gives a radius-
independent scalar prefix after passing to the limit subsequence.  The source
slabs may still be supplied separately for each radius; all of them use the
same `D = max 4 (B + 1)` (Claim 11.17, pp. 277--278). -/
theorem eventually_uniform_prefix_scalar_of_finite_limit
    {S : GeneralizedBlowupSequence.{u}} {T : ℝ}
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (_hT : 0 < T)
    {Tplus kappa r₀ : ℝ} (hTTplus : T < Tplus)
    (hslabs : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      Nonempty (M30FiniteHorizonSlab S k A Tplus kappa r₀))
    (hscalar : ∃ B : ℝ, 0 ≤ B ∧
      ∀ s, s ∈ Ioc (-T) 0 → ∀ x : G.limit.carrier.carrier,
        (G.limit.flow.connection s).scalarCurvature x ≤ B) :
    ∃ D : ℝ, 4 ≤ D ∧
      ∀ A : ℝ, 0 < A → ∀ t : ℝ, 0 < t → ∀ htT : t < T,
        ∀ᶠ k : ℕ in atTop,
          ∃ e : M30FiniteHorizonSlab
              (reindexedBlowupSequence S G.subsequence G.subsequence_strictMono)
              k A Tplus kappa r₀,
            ∀ s (hs : s ∈ Icc (-t) 0)
              (x : (((reindexedBlowupSequence S G.subsequence
                G.subsequence_strictMono).flow k).slice
                ((reindexedBlowupSequence S G.subsequence
                  G.subsequence_strictMono).base k).1).carrier),
              x ∈ (reindexedBlowupSequence S G.subsequence
                G.subsequence_strictMono).baseBall k A →
                ((reindexedBlowupSequence S G.subsequence
                  G.subsequence_strictMono).flow k).scalar
                  ((FiniteHorizonSlab.closedEmbedding e
                    (htT.trans hTTplus)).pointMap s hs x) ≤
                  D * (reindexedBlowupSequence S G.subsequence
                    G.subsequence_strictMono).scale k := by
  obtain ⟨B, hB, hscalar⟩ := hscalar
  let S' : GeneralizedBlowupSequence.{u} :=
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
  let D : ℝ := max 4 (B + 1)
  have hD : 4 ≤ D := le_max_left _ _
  refine ⟨D, hD, ?_⟩
  intro A hA t ht htT
  have hslabs' : ∀ᶠ k : ℕ in atTop,
      Nonempty (M30FiniteHorizonSlab S' k A Tplus kappa r₀) := by
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually
      (hslabs A hA)] with k hk
    obtain ⟨e⟩ := hk
    exact ⟨{
      embedding := e.embedding
      zero_identity := e.zero_identity
      noncollapsed := e.noncollapsed }⟩
  have hprefix := eventually_finiteSlab_prefix_scalar_of_limit_bound
    (S := S') (T := T) G' hA hTTplus hslabs' (by
      intro s hs x hx
      exact hscalar s hs x)
      t ht htT
  filter_upwards [hprefix] with k hk
  obtain ⟨e, he⟩ := hk
  refine ⟨e, ?_⟩
  intro s hs x hx
  simpa only [D, S', G', reindexedBlowupSequence, Function.id_def,
    GeneralizedBlowupSequence.scale, GeneralizedBlowupSequence.baseBall] using
    he s hs x hx

end PoincareMT.M30
