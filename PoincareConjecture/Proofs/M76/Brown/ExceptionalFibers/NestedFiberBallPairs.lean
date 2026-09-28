import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

open Set Metric

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [MetricSpace X]

theorem exists_nested_ballPairs_of_cofinal {A : Set X} (hA : IsClosed A)
    (hAne : A.Nonempty)
    (hcofinal : ∀ U : Set X, IsOpen U → A ⊆ U →
      ∃ K : Set X, IsCompact K ∧ A ⊆ interior K ∧ K ⊆ U ∧
        IsUnitBallPair E K (frontier K))
    {U : Set X} (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧
      (∀ n, A ⊆ interior (K n)) ∧ (∀ n, K (n + 1) ⊆ interior (K n)) ∧
      (∀ n, IsUnitBallPair E (K n) (frontier (K n))) ∧ K 0 ⊆ U ∧
      (⋂ n, K n) = A := by
  classical
  let Cells := {K : Set X // IsCompact K ∧ A ⊆ interior K ∧
    IsUnitBallPair E K (frontier K)}
  have hpos (n : ℕ) : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  have hstep (n : ℕ) (K : Cells) : ∃ L : Cells,
      (L : Set X) ⊆ interior (K : Set X) ∧
      (L : Set X) ⊆ {x | infDist x A < (1 : ℝ) / ((n : ℝ) + 1)} := by
    let W := interior (K : Set X) ∩
      {x | infDist x A < (1 : ℝ) / ((n : ℝ) + 1)}
    have hW : IsOpen W := isOpen_interior.inter
      (isOpen_lt (continuous_infDist_pt A) continuous_const)
    have hAW : A ⊆ W := by
      intro x hx
      refine ⟨K.property.2.1 hx, ?_⟩
      change infDist x A < (1 : ℝ) / ((n : ℝ) + 1)
      rw [infDist_zero_of_mem hx]
      exact hpos n
    obtain ⟨L, hL, hAL, hLW, hLpair⟩ := hcofinal W hW hAW
    exact ⟨⟨L, hL, hAL, hLpair⟩, fun x hx => (hLW hx).1, fun x hx => (hLW hx).2⟩
  choose next hnext hdist using hstep
  obtain ⟨K0, hK0, hAK0, hK0U, hK0pair⟩ := hcofinal U hU hAU
  let K : ℕ → Cells := Nat.rec ⟨K0, hK0, hAK0, hK0pair⟩ (fun n Kn => next n Kn)
  refine ⟨fun n : ℕ => (K n).val, ?_⟩
  refine ⟨fun n => (K n).property.1,
    fun n => (K n).property.2.1, fun n => hnext n (K n),
    fun n => (K n).property.2.2, ?_, ?_⟩
  · change K0 ⊆ U
    exact hK0U
  ext x
  constructor
  · intro hx
    by_contra hxA
    have hp : 0 < infDist x A := (hA.notMem_iff_infDist_pos hAne).mp hxA
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hp
    have hxN : x ∈ (K (n + 1) : Set X) := mem_iInter.mp hx (n + 1)
    have hs := hdist n (K n) hxN
    exact lt_asymm hn hs
  · intro hx
    exact mem_iInter.mpr fun n => interior_subset ((K n).property.2.1 hx)

end Set
