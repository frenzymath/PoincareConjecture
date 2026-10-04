import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.GeneralizedLimit.GeneralizedCompactPreimages
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.GeneralizedLimit.GeneralizedScalarConvergence
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.WorldlineUniqueness
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data

/-!
# Uniform scalar bounds on shorter source prefixes

Morgan--Tian Claim 11.17, pp. 277--278, transfers the compact limit bound
to the supplied source cylinders before applying the scalar differential
estimate. Fixed compact preimages and actual worldline uniqueness retain
one cylinder and one scalar coefficient on every shorter time prefix.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

/-- A scalar bound on a compact spatial set over one closed time prefix
transfers to the supplied source slab on that prefix (Claim 11.17,
pp. 277--278). -/
theorem eventually_finiteSlab_scalar_of_generalized_limit_bound_on_prefix
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J)
    {A Tplus kappa r0 B : ℝ} (hA : 0 < A)
    (hslabs : ∀ᶠ n in atTop,
      Nonempty (M30FiniteHorizonSlab S n A Tplus kappa r0))
    (t : ℝ) (ht : 0 < t) (htTplus : t < Tplus) (hI : Icc (-t) 0 ⊆ J)
    (hscalar : ∀ s ∈ Icc (-t) 0,
      ∀ x ∈ closure ((G.limit.flow.metric 0).ball G.limit.base (2 * A)),
        (G.limit.flow.connection s).scalarCurvature x ≤ B) :
    ∀ᶠ k in atTop,
        ∃ e : M30FiniteHorizonSlab S (G.subsequence k) A Tplus kappa r0,
          ∀ s (hs : s ∈ Icc (-t) 0)
            (x : ((S.flow (G.subsequence k)).slice
              (S.base (G.subsequence k)).1).carrier),
            x ∈ S.baseBall (G.subsequence k) A →
              (S.flow (G.subsequence k)).scalar
                ((FiniteHorizonSlab.closedEmbedding e
                  htTplus).pointMap s hs x) ≤
                max 4 (B + 1) * S.scale (G.subsequence k) := by
  let g := G.limit.flow.metric 0
  let : MetricSpace G.limit.carrier.carrier := G.limit.carrier.metricSpaceOf g
  let K := closure (g.ball G.limit.base (2 * A))
  have hK : IsCompact K := by
    apply IsCompact.of_isClosed_subset
      (g.isCompact_closedBall_of_metricComplete
        (G.limit.complete 0 G.limit.zero_mem) G.limit.base (2 * A)) isClosed_closure
    apply closure_minimal
      (fun x (hx : g.edist G.limit.base x < ENNReal.ofReal (2 * A)) => hx.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hslabs' := G.subsequence_strictMono.tendsto_atTop.eventually hslabs
  filter_upwards [eventually_generalized_terminal_baseBall_preimage_ball G hA,
    eventually_generalized_scalar_error G isCompact_Icc hI hK zero_lt_one,
    hslabs'] with k hcapture herr he
  obtain ⟨e⟩ := he
  refine ⟨e, ?_⟩
  intro s hs x hx
  obtain ⟨y, hy, hzero⟩ := hcapture.2 x hx
  have hyK : y ∈ K := subset_closure hy
  have h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have h0t : (0 : ℝ) ∈ Icc (-t) 0 := ⟨neg_nonpos.mpr ht.le, le_rfl⟩
  have hmeet : (G.embedding k).pointMap 0 h0 y =
      (FiniteHorizonSlab.closedEmbedding e htTplus).pointMap 0 h0t x :=
    (hzero h0).trans
      (FiniteHorizonSlab.closedEmbedding_zero_identity e htTplus h0t x hx).symm
  have hpoint := Cylinder.pointMap_eq_on_overlap (G.embedding k)
    (FiniteHorizonSlab.closedEmbedding e htTplus)
    ordConnected_Icc ordConnected_Icc (herr.2.1 hyK) hx h0 h0t hmeet s (herr.1 hs) hs
  have herror := (abs_lt.mp (herr.2.2 s hs (herr.1 hs) y hyK)).2
  have hbound := hscalar s hs y hyK
  have hQ := S.base_scalar_pos (G.subsequence k)
  rw [← hpoint]
  apply (div_le_iff₀ hQ).mp
  exact (show (S.flow (G.subsequence k)).scalar
      ((G.embedding k).pointMap s (herr.1 hs) y) / S.scale (G.subsequence k) ≤
        B + 1 by linarith).trans (le_max_right _ _)

/-- The finite-horizon specialization of source scalar transfer on one
closed prefix (Claim 11.17, pp. 277--278). -/
theorem eventually_finiteSlab_scalar_of_limit_bound_on_prefix
    {S : GeneralizedBlowupSequence.{u}} {T : ℝ}
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    {A Tplus kappa r0 B : ℝ} (hA : 0 < A) (hTTplus : T < Tplus)
    (hslabs : ∀ᶠ n in atTop,
      Nonempty (M30FiniteHorizonSlab S n A Tplus kappa r0))
    (t : ℝ) (ht : 0 < t) (htT : t < T)
    (hscalar : ∀ s ∈ Icc (-t) 0,
      ∀ x ∈ closure ((G.limit.flow.metric 0).ball G.limit.base (2 * A)),
        (G.limit.flow.connection s).scalarCurvature x ≤ B) :
    ∀ᶠ k in atTop,
        ∃ e : M30FiniteHorizonSlab S (G.subsequence k) A Tplus kappa r0,
          ∀ s (hs : s ∈ Icc (-t) 0)
            (x : ((S.flow (G.subsequence k)).slice
              (S.base (G.subsequence k)).1).carrier),
            x ∈ S.baseBall (G.subsequence k) A →
              (S.flow (G.subsequence k)).scalar
                ((FiniteHorizonSlab.closedEmbedding e
                  (htT.trans hTTplus)).pointMap s hs x) ≤
                max 4 (B + 1) * S.scale (G.subsequence k) := by
  exact eventually_finiteSlab_scalar_of_generalized_limit_bound_on_prefix G hA hslabs
    t ht (htT.trans hTTplus) (closedSlab_subset_openSlab htT) hscalar

/-- A bound on one fixed compact terminal limit ball transfers to every
shorter source prefix with a coefficient independent of its duration
(Claim 11.17, pp. 277--278). -/
theorem eventually_finiteSlab_prefix_scalar_of_limit_bound
    {S : GeneralizedBlowupSequence.{u}} {T : ℝ}
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    {A Tplus kappa r0 B : ℝ} (hA : 0 < A) (hTTplus : T < Tplus)
    (hslabs : ∀ᶠ n in atTop,
      Nonempty (M30FiniteHorizonSlab S n A Tplus kappa r0))
    (hscalar : ∀ s ∈ Ioc (-T) 0,
      ∀ x ∈ closure ((G.limit.flow.metric 0).ball G.limit.base (2 * A)),
        (G.limit.flow.connection s).scalarCurvature x ≤ B) :
    ∀ t : ℝ, 0 < t → ∀ htT : t < T,
      ∀ᶠ k in atTop,
        ∃ e : M30FiniteHorizonSlab S (G.subsequence k) A Tplus kappa r0,
          ∀ s (hs : s ∈ Icc (-t) 0)
            (x : ((S.flow (G.subsequence k)).slice
              (S.base (G.subsequence k)).1).carrier),
            x ∈ S.baseBall (G.subsequence k) A →
              (S.flow (G.subsequence k)).scalar
                ((FiniteHorizonSlab.closedEmbedding e
                  (htT.trans hTTplus)).pointMap s hs x) ≤
                max 4 (B + 1) * S.scale (G.subsequence k) := by
  intro t ht htT
  apply eventually_finiteSlab_scalar_of_limit_bound_on_prefix G hA hTTplus hslabs t ht htT
  intro s hs x hx
  exact hscalar s ⟨by linarith [hs.1], hs.2⟩ x hx

end PoincareMT.M30
