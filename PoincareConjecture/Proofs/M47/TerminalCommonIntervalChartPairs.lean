import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoordinateExtraction








set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCommonInterval_countable_chart_pairs
    {M : Type u} {N : Type v}
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace E N]
    (d : M → N) (hd : Continuous d)
    (a : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    (b : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) N E ∞)
    (ha : ∀ x : M, ∃ i, x ∈ (a i).source)
    (hb : ∀ y : N, ∃ j, y ∈ (b j).source) :
    let a' := fun i => a (Nat.unpair i).1
    let b' := fun i => b (Nat.unpair i).2
    let U := fun i => (a' i).target ∩
      (a' i).symm ⁻¹' (d ⁻¹' (b' i).source)
    (∀ i, IsOpen (U i)) ∧
      (∀ i, U i ⊆ (a' i).target) ∧
      (∀ i, MapsTo (fun x => d ((a' i).symm x)) (U i) (b' i).source) ∧
      ∀ x : M, ∃ i, x ∈ (a' i).source ∧ a' i x ∈ U i := by
  dsimp only
  refine ⟨?_, fun _ _ hx => hx.1, fun _ _ hx => hx.2, ?_⟩
  · intro i
    exact ContinuousOn.isOpen_inter_preimage
      (a (Nat.unpair i).1).toOpenPartialHomeomorph.continuousOn_invFun
      (a (Nat.unpair i).1).open_target
        (hd.isOpen_preimage _ (b (Nat.unpair i).2).open_source)
  · intro x
    obtain ⟨i, hi⟩ := ha x
    obtain ⟨j, hj⟩ := hb (d x)
    refine ⟨Nat.pair i j, ?_⟩
    simp only [Nat.unpair_pair]
    refine ⟨hi, (a i).map_source hi, ?_⟩
    have hai : (a i).symm (a i x) = x := (a i).toPartialEquiv.left_inv hi
    change d ((a i).symm (a i x)) ∈ (b j).source
    rw [hai]
    exact hj

end PoincareConjecture.M47
