import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.CompactTwoFiberCells
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.NestedFiberBallPairs
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.SpherePunctureCharts











set_option autoImplicit false

open Set Metric

namespace ContinuousMap

variable {X Y : Type*} [MetricSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [RegularSpace Y]





theorem exists_sphere_two_fiber_cellular_sequences (q : C(X, Y))
    (hq : Function.Surjective q) (a b : Y) (hab : a ≠ b)
    (hfib : ∀ x y, q x = q y ↔ x = y ∨
      (q x = a ∧ q y = a) ∨ (q x = b ∧ q y = b))
    (eX : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (eY : Y ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (p : X) (hpa : q p ≠ a) (hpb : q p ≠ b)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hAU : q ⁻¹' {a} ⊆ U) (hBV : q ⁻¹' {b} ⊆ V) :
    ∃ K L : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ (∀ n, IsCompact (L n)) ∧
      (∀ n, K (n + 1) ⊆ interior (K n)) ∧
      (∀ n, L (n + 1) ⊆ interior (L n)) ∧
      (∀ n, IsUnitBallPair (Fin 3 → ℝ) (K n) (frontier (K n))) ∧
      (∀ n, IsUnitBallPair (Fin 3 → ℝ) (L n) (frontier (L n))) ∧
      Disjoint (K 0) (L 0) ∧ K 0 ⊆ U ∧ L 0 ⊆ V ∧
      (⋂ n, K n) = q ⁻¹' {a} ∧ (⋂ n, L n) = q ⁻¹' {b} := by
  obtain ⟨C, hCs, hCt⟩ := eX.exists_punctured_three_space_chart p
  obtain ⟨D, hDs, hDt⟩ := eY.exists_punctured_three_space_chart (q p)
  have hfibswap (x y : X) : q x = q y ↔ x = y ∨
      (q x = b ∧ q y = b) ∨ (q x = a ∧ q y = a) :=
    (hfib x y).trans (or_congr Iff.rfl or_comm)
  have hA : IsClosed (q ⁻¹' {a}) := isClosed_singleton.preimage q.continuous
  have hB : IsClosed (q ⁻¹' {b}) := isClosed_singleton.preimage q.continuous
  have hAne : (q ⁻¹' {a}).Nonempty := hq a
  have hBne : (q ⁻¹' {b}).Nonempty := hq b
  have hcoA : ∀ W : Set X, IsOpen W → q ⁻¹' {a} ⊆ W →
      ∃ K : Set X, IsCompact K ∧ q ⁻¹' {a} ⊆ interior K ∧ K ⊆ W ∧
        IsUnitBallPair (Fin 3 → ℝ) K (frontier K) := by
    intro W hW hAW
    exact q.exists_compact_second_fiber_ballPair_subset hq b a hab.symm hfibswap
      p hpb hpa C hCs hCt D hDs hDt hW hAW
  have hcoB : ∀ W : Set X, IsOpen W → q ⁻¹' {b} ⊆ W →
      ∃ K : Set X, IsCompact K ∧ q ⁻¹' {b} ⊆ interior K ∧ K ⊆ W ∧
        IsUnitBallPair (Fin 3 → ℝ) K (frontier K) := by
    intro W hW hBW
    exact q.exists_compact_second_fiber_ballPair_subset hq a b hab hfib
      p hpa hpb C hCs hCt D hDs hDt hW hBW
  obtain ⟨K, hK, _, hnestK, hpairK, hK0, hKA⟩ :=
    exists_nested_ballPairs_of_cofinal hA hAne hcoA hU hAU
  obtain ⟨L, hL, _, hnestL, hpairL, hL0, hLB⟩ :=
    exists_nested_ballPairs_of_cofinal hB hBne hcoB hV hBV
  exact ⟨K, L, hK, hL, hnestK, hnestL, hpairK, hpairL,
    hUV.mono hK0 hL0, hK0, hL0, hKA, hLB⟩

end ContinuousMap
