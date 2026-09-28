import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Caps.Extrema
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.CriticalLevels.Cardinality

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Nested
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_unique_critical_in_each_cap :
    ∃ p : Fin 3 → S2, ∀ i, p i ∈ capRegion i ∧
      mfderiv (𝓡 2) 𝓘(Real, Real) height (p i)=0 ∧
      ∀ q ∈ capRegion i, mfderiv (𝓡 2) 𝓘(Real, Real) height q=0 → q=p i := by
  classical
  choose p hp hpc using exists_critical_in_capRegion
  obtain ⟨p₀, hp₀, hc₀, _⟩ := retainedBand_unique_critical_point
  let C := {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) height p=0}
  let : Fintype C := finite_critical_points.fintype
  have hsub (i : Fin 3) : capRegion i ⊆ retainedBandᶜ :=
    fun q hq => capRegion_cover.subset (mem_iUnion_of_mem i hq)
  let f : Option (Fin 3) → C
    | none => ⟨p₀, hc₀⟩
    | some i => ⟨p i, hpc i⟩
  have hf : Injective f := by
    intro i j hij
    have heq := congrArg Subtype.val hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        change p₀=p j at heq
        exact (hsub j (hp j) (heq ▸ hp₀)).elim
    | some i =>
      cases j with
      | none =>
        change p i=p₀ at heq
        exact (hsub i (hp i) (heq.symm ▸ hp₀)).elim
      | some j =>
        change p i=p j at heq
        have he : i=j := by
          by_contra hne
          exact disjoint_left.mp (capRegion_disjoint hne) (hp i) (heq.symm ▸ hp j)
        exact congrArg some he
  have hsurj : Surjective f :=
    (hf.bijective_of_nat_card_le (by simpa [C] using card_critical_points_le_four)).2
  refine ⟨p, fun i => ⟨hp i, hpc i, ?_⟩⟩
  intro q hq hqc
  obtain ⟨j, hj⟩ := hsurj ⟨q, hqc⟩
  have heq := congrArg Subtype.val hj
  cases j with
  | none =>
    change p₀=q at heq
    exact (hsub i hq (heq ▸ hp₀)).elim
  | some j =>
    change p j=q at heq
    have hji : j=i := by
      by_contra hne
      exact disjoint_left.mp (capRegion_disjoint hne) (hp j) (heq.symm ▸ hq)
    exact heq.symm.trans (congrArg p hji)

end Poincare.Manifold.Schoenflies.Saddle.Nested

end

end M38Schoenflies
