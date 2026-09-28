import PoincareConjecture.Proofs.M47.LimitNoncollapseSourceCenters
import PoincareConjecture.Proofs.M47.LimitNoncollapseWorldlines
import PoincareConjecture.Statements.M47CanonicalInduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem limitNoncollapse_eventually_source_noncollapsed
    (P : M47Predecessors.{u}) {S : GeneralizedBlowupSequence.{u}} {H : ENNReal}
    (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))
    {T kappa r0 : ℝ} (hT : 0 < T) (hTH : ENNReal.ofReal T < H)
    (hslabs : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      Nonempty (M30FiniteHorizonSlab S k A T kappa r0))
    (p : G.limit.sliceCarrier.carrier)
    {Ktime : Set ℝ} (hKtime : IsCompact Ktime) (hKT : Ktime ⊆ Ioc (-T) 0) :
    ∀ᶠ k : ℕ in atTop,
      Ktime ⊆ Icc (-G.exhaustion.time k) 0 ∧
      p ∈ G.exhaustion.space k ∧
      ∀ s ∈ Ktime, ∀ hs : s ∈ Icc (-G.exhaustion.time k) 0,
        GeneralizedKappaNoncollapsedAt (S.flow (G.subsequence k))
          ((G.embedding k).pointMap s hs p) kappa r0 := by
  classical
  have hKJ : Ktime ⊆ blowupBackwardInterval H := by
    intro s hs
    have ht := hKT hs
    exact ⟨ht.2, (ENNReal.ofReal_le_ofReal (by linarith [ht.1])).trans_lt hTH⟩
  obtain ⟨A, hA, hcenter⟩ := limitNoncollapse_eventually_source_center G p
  have hD := G.subsequence_strictMono.tendsto_atTop.eventually (hslabs A hA)
  filter_upwards [hcenter, hD, G.exhaustion.time_cofinal Ktime hKtime hKJ]
    with k hk hslab htime
  obtain ⟨D⟩ := hslab
  let h0 : 0 ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  obtain ⟨y, hy, heq⟩ := hk.2 h0
  refine ⟨htime, hk.1, ?_⟩
  intro s hs hsk
  exact limitNoncollapse_at_of_slab P.m11 hT (G.exhaustion.time_pos k) D
    (G.exhaustion.space_open k) (G.embedding k) p hk.1 y hy heq s hsk (hKT hs)

end PoincareConjecture.M47
