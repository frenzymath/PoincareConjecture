import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskSignedFiber









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_finitePL_fiber_of_paired_ends {N : Set E} {a z q : E}
    (hN : IsFinitePLBallPair ℝ N {a, z}) (f : E → ℝ)
    (hf : ContinuousOn f N) (hzero : N ∩ {x | f x = 0} = {q})
    (hsign : (f a < 0 ∧ 0 < f z) ∨ (0 < f a ∧ f z < 0)) :
    ∃ F : ℝ → E, FinitePiecewiseAffineOn F I ∧ InjOn F I ∧ F '' I = N ∧
      F 0 = q ∧ (∀ t ∈ I, F t ∈ ({a, z} : Set E) ↔ t ∈ ({-1, 1} : Set ℝ)) ∧
      (∀ t ∈ I, 0 ≤ f (F t) ↔ 0 ≤ t) ∧
      ∀ t ∈ I, f (F t) ≤ 0 ↔ t ≤ 0 := by
  have hordered {an ap : E} (hpair : IsFinitePLBallPair ℝ N {an, ap})
      (hn : f an < 0) (hp : 0 < f ap) :
      ∃ F : ℝ → E, FinitePiecewiseAffineOn F I ∧ InjOn F I ∧ F '' I = N ∧
        F 0 = q ∧ (∀ t ∈ I, F t ∈ ({an, ap} : Set E) ↔
          t ∈ ({-1, 1} : Set ℝ)) ∧
        (∀ t ∈ I, 0 ≤ f (F t) ↔ 0 ≤ t) ∧
        ∀ t ∈ I, f (F t) ≤ 0 ↔ t ≤ 0 := by
    obtain ⟨F, hF, hi, him, h0, hnval, hpval, hpos, hneg⟩ :=
      HamiltonIndexOne.exists_signed_interval_fiber hpair f hf hzero hn hp
    refine ⟨F, hF, hi, him, h0, ?_, hpos, hneg⟩
    intro t ht
    constructor
    · rintro (he | he)
      · exact Or.inl (hi ht (by norm_num) (he.trans hnval.symm))
      · exact Or.inr (hi ht (by norm_num) (he.trans hpval.symm))
    · rintro (rfl | rfl)
      · exact Or.inl hnval
      · exact Or.inr hpval
  rcases hsign with h | h
  · exact hordered hN h.1 h.2
  · obtain ⟨F, hF, hi, him, h0, hrim, hpos, hneg⟩ :=
      hordered (by simpa only [pair_comm] using hN) h.2 h.1
    exact ⟨F, hF, hi, him, h0, by simpa only [pair_comm] using hrim, hpos, hneg⟩

end PoincareConjecture.M76
