import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Uniform interior height bounds on compact cylinders

A continuous height map whose whole unit-cylinder image
lies strictly inside the unit interval has a uniform smaller
bound on each closed thinner cylinder over a compact base.
This verifies the normalization in the Edwards reconstruction
of Hamilton's torus immersion, p. 66. See M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace StableCylinder

/-- Compactness supplies an actual uniform rotation-core
height bound after the thin source interval has been fixed.
The empty-base case is allowed. No assertion is made on the
closed boundary of the original unit cylinder. See M76
derivation 270, stable circle-target conjugation. -/
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
