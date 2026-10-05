import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Noncollapse.LimitNoncollapseFiniteHarnackDomain
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSequence

/-!
# Positive physical clocks from a finite left buffer

A forward point inhabits the actual physical slice. A strictly earlier
included normalized time then proves strict positivity in a nonnegative
history interval. Source: MT Proposition 17.1; reviewed compact transfer F2d.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareMT.M47

/-- The actual forward point certifies membership of its dependent
physical clock in the original generalized interval. -/
theorem limitNoncollapse_physical_time_mem
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (-G.exhaustion.time k) 0) :
    (S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k) ∈
      (S.flow (G.subsequence k)).interval := by
  apply ((S.flow (G.subsequence k)).slice_nonempty_iff _).mp
  exact ⟨(G.embedding k).forward t ht G.limit.base⟩

/-- The finite left buffer gives a strictly positive physical time,
including when the tested normalized time is zero. -/
theorem limitNoncollapse_eventually_physical_time_pos
    {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
    (hfinite : H ≠ ⊤)
    (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))
    (hnonnegative : ∀ k, (S.flow k).interval ⊆ Ici 0)
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H) :
    ∀ᶠ k : ℕ in atTop,
      t ∈ Icc (-G.exhaustion.time k) 0 ∧
      (S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k) ∈
        (S.flow (G.subsequence k)).interval ∧
      0 < (S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k) := by
  have ht' : -H.toReal < t ∧ t ≤ 0 := by
    rwa [limitFinite_domain_eq hfinite] at ht
  let a := (t - H.toReal) / 2
  have hat : a < t := by dsimp [a]; linarith
  have ha : a ∈ blowupBackwardInterval H := by
    rw [limitFinite_domain_eq hfinite]
    dsimp [a]
    constructor <;> linarith
  have hpair : ({a, t} : Set ℝ) ⊆ blowupBackwardInterval H := by
    intro s hs
    rcases mem_insert_iff.mp hs with rfl | hs
    · exact ha
    · exact mem_singleton_iff.mp hs ▸ ht
  filter_upwards [G.exhaustion.time_cofinal {a, t}
    ((isCompact_singleton : IsCompact ({t} : Set ℝ)).insert a) hpair] with k hk
  have hak : a ∈ Icc (-G.exhaustion.time k) 0 := hk (by simp)
  have htk : t ∈ Icc (-G.exhaustion.time k) 0 := hk (by simp)
  refine ⟨htk, limitNoncollapse_physical_time_mem G k t htk, ?_⟩
  have hnonneg := hnonnegative (G.subsequence k)
    (limitNoncollapse_physical_time_mem G k a hak)
  have hdiv := (div_lt_div_iff_of_pos_right (G.embedding k).scale_pos).mpr hat
  change 0 ≤ (S.base (G.subsequence k)).1 + a / S.scale (G.subsequence k) at hnonneg
  linarith

end PoincareMT.M47
