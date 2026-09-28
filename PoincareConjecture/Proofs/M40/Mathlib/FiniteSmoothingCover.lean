import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

universe uE uH uM

namespace PoincareConjecture.Proofs.M40

noncomputable section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [CompactSpace M] [IsManifold I ∞ M]

theorem exists_finite_smoothBumpCovering
    (U : M → Set M) (hU : ∀ x : M, U x ∈ 𝓝 x) :
    ∃ (n : ℕ) (c : Fin n → M) (ρ : ∀ i, SmoothBumpFunction I (c i)),
      (∀ i, tsupport (ρ i) ⊆ U (c i)) ∧
      (∀ i, ContMDiff I 𝓘(ℝ) ∞ (ρ i)) ∧
      (∀ x : M, ∃ i, (ρ i : M → ℝ) =ᶠ[𝓝 x] 1) := by
  obtain ⟨ι, b, hb⟩ := SmoothBumpCovering.exists_isSubordinate I
    (s := (Set.univ : Set M)) isClosed_univ (fun x _ => hU x)
  letI : Fintype ι := b.fintype
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, (fun i => b.c (e i)), (fun i => b (e i)),
    (fun i => hb (e i)), (fun i => (b (e i)).contMDiff), ?_⟩
  intro x
  obtain ⟨i, hi⟩ := b.eventuallyEq_one' x (Set.mem_univ x)
  obtain ⟨j, rfl⟩ := e.surjective i
  exact ⟨j, hi⟩

end

end PoincareConjecture.Proofs.M40
