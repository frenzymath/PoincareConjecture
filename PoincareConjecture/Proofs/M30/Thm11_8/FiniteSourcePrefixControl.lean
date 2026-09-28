import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSourcePrefix
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSlabControlled
import PoincareConjecture.Proofs.M30.Thm5_33.CurvatureNorm










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold



theorem eventually_controlled_prefix_of_finite_scalar_bound
    (hC : RicciFlowCurvatureTheory.{u})
    {S : GeneralizedBlowupSequence.{u}} {T t Tplus B : ℝ}
    {epsilon C kappa r0 mu : ℝ}
    (H : M30CommonBlowupControls S epsilon C kappa r0 mu)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (hTplus : T < Tplus)
    (hslabs : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      Nonempty (M30FiniteHorizonSlab S k A Tplus kappa r0))
    (ht : 0 < t) (htT : t < T)
    (hscalar : ∀ s ∈ Icc (-t) 0, ∀ x,
      (G.limit.flow.connection s).scalarCurvature x ≤ B) :
    ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k : ℕ in atTop,
        Nonempty (ControlledBlowupCylinder S (G.subsequence k)
          A t (13 * max 4 (B + 1)) eta) := by
  intro A hA eta heta
  have hprefix := eventually_finiteSlab_scalar_of_limit_bound_on_prefix
    G hA hTplus (hslabs A hA) t ht htT (fun s hs x _hx => hscalar s hs x)
  have hD : 0 ≤ max 4 (B + 1) := le_trans (by norm_num) (le_max_left _ _)
  have hpinch := G.subsequence_strictMono.tendsto_atTop.eventually
    (eventually_curvatureNorm_and_negativeDefect_le hC S H.branch
      (max 4 (B + 1)) hD eta heta)
  filter_upwards [hprefix, hpinch] with k hk hpinchK
  obtain ⟨e, he⟩ := hk
  have hmax : max (max 4 (B + 1)) 1 = max 4 (B + 1) :=
    max_eq_left (le_trans (by norm_num) (le_max_left _ _))
  refine ⟨controlledCylinderOfFiniteHorizonSlab e (htT.trans hTplus) ?_ ?_⟩
  · intro s hs x hx
    let p := (FiniteHorizonSlab.closedEmbedding e (htT.trans hTplus)).pointMap s hs x
    have hp : p.1 ∈ (S.flow (G.subsequence k)).interval :=
      ((S.flow (G.subsequence k)).slice_nonempty_iff p.1).mp ⟨p.2⟩
    have h := (hpinchK p.1 hp p.2 (he s hs x hx)).1
    simpa only [hmax] using h
  · intro s hs x hx
    let p := (FiniteHorizonSlab.closedEmbedding e (htT.trans hTplus)).pointMap s hs x
    have hp : p.1 ∈ (S.flow (G.subsequence k)).interval :=
      ((S.flow (G.subsequence k)).slice_nonempty_iff p.1).mp ⟨p.2⟩
    exact (hpinchK p.1 hp p.2 (he s hs x hx)).2

end PoincareConjecture.M30
