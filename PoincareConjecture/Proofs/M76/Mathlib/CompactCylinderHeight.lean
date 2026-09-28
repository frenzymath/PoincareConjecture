import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

set_option autoImplicit false

open Set

namespace StableCylinder

theorem exists_uniform_height_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (v : X × ℝ → ℝ) (hv : ContinuousOn v (univ ×ˢ Ioo (-1) 1))
    (hunit : ∀ z ∈ univ ×ˢ Ioo (-1) 1, |v z| < 1)
    {delta : ℝ} (_hd : 0 < delta) (hd1 : delta < 1) :
    ∃ a : ℝ, delta < a ∧ a < 1 ∧
      ∀ z ∈ univ ×ˢ Icc (-delta) delta, |v z| < a := by
  let K : Set (X × ℝ) := univ ×ˢ Icc (-delta) delta
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hKU : K ⊆ univ ×ˢ Ioo (-1) 1 := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    constructor <;> linarith [hz.2.1, hz.2.2]
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨(delta + 1) / 2, by linarith, by linarith, ?_⟩
    intro z hz
    exact (show z ∈ (∅ : Set (X × ℝ)) from hKe ▸ hz).elim
  · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hKne ((hv.mono hKU).abs)
    have hm : max delta |v z| < 1 := max_lt hd1 (hunit z (hKU hz))
    let a := (max delta |v z| + 1) / 2
    have hma : max delta |v z| < a := by dsimp only [a]; linarith
    refine ⟨a, (le_max_left _ _).trans_lt hma, ?_, ?_⟩
    · dsimp only [a]
      linarith
    · intro y hy
      exact (hmax hy).trans_lt ((le_max_right _ _).trans_lt hma)

end StableCylinder
