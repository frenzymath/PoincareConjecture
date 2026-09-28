import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.CriticalLevels.Finite
import Mathlib.Tactic.ComputeDegree



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem card_critical_points_le_four :
    Nat.card {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) height p=0} ≤ 4 := by
  classical
  let P : Polynomial Real :=
    (1-Polynomial.X^2)*(2*Polynomial.X-1)^2-Polynomial.C (9/100)*Polynomial.X^2
  have hP : P ≠ 0 := by
    intro hp
    have h := congrArg (Polynomial.eval (0 : Real)) hp
    norm_num [P] at h
  have hdegree : P.natDegree ≤ 4 := by
    dsimp [P]
    compute_degree
  let f : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) height p=0} → ↑P.roots.toFinset :=
    fun p => ⟨(p.val : E3) 2, by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      change Polynomial.eval _ P=0
      simpa [P, criticalPolynomial] using critical_polynomial_eq_zero p.property⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply critical_latitude_injOn p.property q.property
    exact congrArg Subtype.val hpq
  calc
    Nat.card {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) height p=0}
        ≤ Nat.card ↑P.roots.toFinset := Nat.card_le_card_of_injective f hf
    _ = P.roots.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ 4 := hdegree

end Poincare.Manifold.Schoenflies.Saddle.Nested
