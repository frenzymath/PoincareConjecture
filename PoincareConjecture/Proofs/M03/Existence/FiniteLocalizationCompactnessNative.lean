import PoincareConjecture.Proofs.M03.Existence.EuclideanRellichNative

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology BigOperators

namespace PoincareConjecture.FiniteLocalizationCompactnessNative

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [NormedSpace ℝ H]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
  [∀ i, CompleteSpace (V i)]

theorem totallyBounded_of_finite_reconstruction {S : Set H}
    (P : ∀ i, H → V i) (Q : ∀ i, V i →L[ℝ] H)
    (hlocal : ∀ i, TotallyBounded (P i '' S))
    (hreconstruct : ∀ u ∈ S, (∑ i, Q i (P i u)) = u) : TotallyBounded S := by
  let K : Set (∀ i, V i) := {z | ∀ i, z i ∈ closure (P i '' S)}
  have hK : IsCompact K :=
    isCompact_pi_infinite (fun i => (hlocal i).closure.isCompact_of_isClosed isClosed_closure)
  let R : (∀ i, V i) → H := fun z => ∑ i, Q i (z i)
  have hR : Continuous R :=
    continuous_finsetSum Finset.univ (fun i _ => (Q i).continuous.comp (continuous_apply i))
  apply (hK.image hR).totallyBounded.subset
  intro u hu
  refine ⟨fun i => P i u, ?_, hreconstruct u hu⟩
  intro i
  exact subset_closure ⟨u, hu, rfl⟩

theorem isCompact_closure_of_finite_reconstruction [CompleteSpace H] {S : Set H}
    (P : ∀ i, H → V i) (Q : ∀ i, V i →L[ℝ] H)
    (hlocal : ∀ i, TotallyBounded (P i '' S))
    (hreconstruct : ∀ u ∈ S, (∑ i, Q i (P i u)) = u) : IsCompact (closure S) :=
  (totallyBounded_of_finite_reconstruction P Q hlocal hreconstruct).closure.isCompact_of_isClosed
    isClosed_closure

end PoincareConjecture.FiniteLocalizationCompactnessNative
