import PoincareConjecture.Proofs.M47.TerminalSourceCountableMaps
import PoincareConjecture.Proofs.M47.TerminalSourceCountableLabels










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)


def terminalSourceCountableCore (rho : ℝ) : Set (terminalSourceCountableDomain rho) :=
  (Subtype.val : terminalSourceCountableDomain rho → E) ⁻¹' closedBall 0 (rho / 4)


theorem terminalSourceCountableCore_compact {rho : ℝ} (hrho : 0 < rho) :
    IsCompact (terminalSourceCountableCore rho) := by
  have hsub : closedBall (0 : E) (rho / 4) ⊆ ball 0 (rho / 2) :=
    closedBall_subset_ball (by linarith)
  have he := (terminalSourceCountableDomain rho).isOpen.isOpenEmbedding_subtypeVal.isEmbedding
  exact he.isInducing.isCompact_preimage' (isCompact_closedBall (0 : E) (rho / 4))
      (fun x hx => ⟨⟨x, hsub hx⟩, rfl⟩)



theorem terminalSourceCountable_core_covers
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    {rho : ℕ → ℝ} {N : ℕ → ℕ} (hrho : ∀ j, 0 < rho j)
    (e : ∀ k j, j ≤ k → Fin (N j + 1) → terminalSourceCountableDomain (rho j) → M k)
    (point : ∀ k, M k)
    (hzero : ∀ k, e k 0 (Nat.zero_le k) 0 (terminalSourceCountableZero (hrho 0)) = point k)
    (A : ℕ → ℝ) (hA : ∀ R : ℝ, 0 < R → ∃ j, R ≤ A j)
    (hcover : ∀ k j hjk,
      ball (point k) (A j) ⊆ ⋃ i, e k j hjk i '' terminalSourceCountableCore (rho j)) :
    let label := terminalSourceCountableLabel N
    let U := fun n => terminalSourceCountableDomain (rho (label n).1)
    let total := fun k n => terminalSourceCountableMap hrho e k (label n).1 (label n).2
    (∀ k, total k 0 (terminalSourceCountableZero (hrho (label 0).1)) = point k) ∧
      ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ, ∃ K : ∀ n, Set (U n),
        (∀ n, K n = terminalSourceCountableCore (rho (label n).1)) ∧
        (∀ n ∈ s, IsCompact (K n)) ∧
          ∀ᶠ k in atTop, ball (point k) R ⊆ ⋃ n ∈ s, total k n '' K n := by
  classical
  let label := terminalSourceCountableLabel N
  let U := fun n => terminalSourceCountableDomain (rho (label n).1)
  let total := fun k n => terminalSourceCountableMap hrho e k (label n).1 (label n).2
  constructor
  · intro k
    have hz := congrArg (fun q : Σ j, Fin (N j + 1) =>
      terminalSourceCountableMap hrho e k q.1 q.2 (terminalSourceCountableZero (hrho q.1)))
        (terminalSourceCountableLabel_zero N)
    apply hz.trans
    rw [terminalSourceCountableMap_good hrho e (Nat.zero_le k)]
    exact hzero k
  · intro R hR
    obtain ⟨j, hj⟩ := hA R hR
    let s : Finset ℕ := Finset.univ.image (fun i : Fin (N j + 1) => Nat.pair j i.val)
    let K : ∀ n, Set (U n) := fun n => terminalSourceCountableCore (rho (label n).1)
    refine ⟨s, K, fun _ => rfl,
      fun n _ => terminalSourceCountableCore_compact (hrho (label n).1), ?_⟩
    filter_upwards [eventually_ge_atTop j] with k hjk y hy
    obtain ⟨i, x, hx, hxy⟩ := mem_iUnion.mp (hcover k j hjk (ball_subset_ball hj hy))
    refine mem_iUnion.mpr ⟨Nat.pair j i.val, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · have heq := congrArg (fun q : Σ j, Fin (N j + 1) =>
        terminalSourceCountableMap hrho e k q.1 q.2 '' terminalSourceCountableCore (rho q.1))
          (terminalSourceCountableLabel_pair N j i)
      apply heq.symm.subset
      rw [terminalSourceCountableMap_good hrho e hjk]
      exact ⟨x, hx, hxy⟩

end PoincareConjecture.M47
