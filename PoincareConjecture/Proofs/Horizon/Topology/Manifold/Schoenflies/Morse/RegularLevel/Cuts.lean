import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.RegularCuts
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.Compact
import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev S2 := Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem exists_finite_regular_cuts_of_distinct_critical_values
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hC : {p | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite)
    (hinj : InjOn h {p | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}) :
    ∃ A : Set Real, A.Finite ∧
      (∀ a ∈ A, ∀ p, h p = a -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0) ∧
      (∀ a ∈ A, Finite (ConnectedComponents (h ⁻¹' {a} : Set S2))) ∧
      ∀ p q, mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0 ->
        mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 ->
        h q ∈ connectedComponentIn Aᶜ (h p) -> p = q := by
  let C : Set S2 := {p | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}
  obtain ⟨A, hA, hdisj, hcuts⟩ :=
    Poincare.Analysis.Calculus.Morse.exists_finite_cuts_between (hC.image h)
  have hregular (a : Real) (ha : a ∈ A) (p : S2) (hp : h p = a) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0 := by
    intro hzero
    exact Set.disjoint_left.mp hdisj ha ⟨p, hzero, hp⟩
  refine ⟨A, hA, hregular, ?_, ?_⟩
  · intro a ha
    exact Poincare.Geometry.Manifold.RegularLevel.finite_connectedComponents_of_compact_regular_level
      (n := 1) hh a ((isClosed_singleton.preimage hh.continuous).isCompact) (hregular a ha)
  · intro p q hp hq hsame
    exact hinj hp hq (Poincare.Analysis.Calculus.Morse.eq_of_same_connected_component_of_cuts
      hcuts ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩ hsame)

end Poincare.Manifold.Schoenflies
