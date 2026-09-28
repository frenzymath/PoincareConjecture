import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology










set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem strict_sign_data_of_finitePL_signed_pairs {c : Set E} (A : E → ℝ)
    (hneg : IsFinitePLBallPair ℝ (c ∩ {x | A x ≤ 0}) (c ∩ {x | A x = 0}))
    (hpos : IsFinitePLBallPair ℝ (c ∩ {x | 0 ≤ A x}) (c ∩ {x | A x = 0})) :
    IsConnected (c ∩ {x | A x < 0}) ∧ IsConnected (c ∩ {x | 0 < A x}) ∧
      ∀ x ∈ c, A x = 0 →
        x ∈ closure (c ∩ {y | A y < 0}) ∧ x ∈ closure (c ∩ {y | 0 < A y}) := by
  have hnset : (c ∩ {x | A x ≤ 0}) \ (c ∩ {x | A x = 0}) =
      c ∩ {x | A x < 0} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, lt_of_le_of_ne hx.1.2 (fun h => hx.2 ⟨hx.1.1, h⟩)⟩
    · intro hx
      have hxA : A x < 0 := hx.2
      exact ⟨⟨hx.1, hxA.le⟩, fun h => hxA.ne h.2⟩
  have hpset : (c ∩ {x | 0 ≤ A x}) \ (c ∩ {x | A x = 0}) =
      c ∩ {x | 0 < A x} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, lt_of_le_of_ne hx.1.2 (fun h => hx.2 ⟨hx.1.1, h.symm⟩)⟩
    · intro hx
      have hxA : 0 < A x := hx.2
      exact ⟨⟨hx.1, hxA.le⟩, fun h => hxA.ne' h.2⟩
  refine ⟨hnset ▸ hneg.isConnected_sdiff, hpset ▸ hpos.isConnected_sdiff, ?_⟩
  intro x hx hxA
  constructor
  · rw [← hnset, hneg.closure_sdiff]
    exact ⟨hx, hxA.le⟩
  · rw [← hpset, hpos.closure_sdiff]
    exact ⟨hx, hxA.ge⟩

end Set

namespace Polygon





theorem strict_sign_data {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (A : E → ℝ) (hA : ContinuousOn A (P.boundary ℝ))
    (hzero : (P.boundary ℝ ∩ {x | A x = 0}).ncard = 2)
    (hneg : ∃ x ∈ P.boundary ℝ, A x < 0)
    (hpos : ∃ x ∈ P.boundary ℝ, 0 < A x) :
    IsConnected (P.boundary ℝ ∩ {x | A x < 0}) ∧
      IsConnected (P.boundary ℝ ∩ {x | 0 < A x}) ∧
      ∀ x ∈ P.boundary ℝ, A x = 0 →
        x ∈ closure (P.boundary ℝ ∩ {y | A y < 0}) ∧
          x ∈ closure (P.boundary ℝ ∩ {y | 0 < A y}) := by
  obtain ⟨a, b, hab, hmarks⟩ := ncard_eq_two.mp hzero
  obtain ⟨hn, hp⟩ := P.isFinitePLBallPair_signed_halves hP hinj A hA hab hmarks hneg hpos
  rw [← hmarks] at hn hp
  exact Set.strict_sign_data_of_finitePL_signed_pairs A hn hp

end Polygon
