import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem critical_source_subsingleton_of_cut_avoidance
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (hdistinct : InjOn
      (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ)
      {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q = 0})
    (C : Set ℝ)
    (hseparate : ∀ p : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun r : UnitTwoSphere => ⟪(u : E3), psi (r, 0)⟫_ℝ) p = 0 →
      ∀ q : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun r : UnitTwoSphere => ⟪(u : E3), psi (r, 0)⟫_ℝ) q = 0 →
      ⟪(u : E3), psi (p, 0)⟫_ℝ < ⟪(u : E3), psi (q, 0)⟫_ℝ →
      ∃ t ∈ C, ⟪(u : E3), psi (p, 0)⟫_ℝ < t ∧
        t < ⟪(u : E3), psi (q, 0)⟫_ℝ)
    (K : Set E3) (hK : IsPreconnected K)
    (havoid : ∀ y ∈ K, ∀ t ∈ C, ⟪(u : E3), y⟫_ℝ ≠ t) :
    {q : UnitTwoSphere |
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q = 0 ∧
      psi (q, 0) ∈ K}.Subsingleton := by
  let f := fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ
  have hH : Continuous (fun y : E3 => ⟪(u : E3), y⟫_ℝ) := by fun_prop
  have hno (p q : UnitTwoSphere)
      (hp : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p = 0 ∧ psi (p, 0) ∈ K)
      (hq : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q = 0 ∧ psi (q, 0) ∈ K)
      (hpq : f p < f q) : False := by
    obtain ⟨t, ht, hpt, htq⟩ := hseparate p hp.1 q hq.1 hpq
    obtain ⟨y, hy, hyt⟩ := hK.intermediate_value hp.2 hq.2 hH.continuousOn
      ⟨hpt.le, htq.le⟩
    exact havoid y hy t ht hyt
  intro p hp q hq
  apply hdistinct hp.1 hq.1
  rcases lt_trichotomy (f p) (f q) with hlt | heq | hgt
  · exact False.elim (hno p q hp hq hlt)
  · exact heq
  · exact False.elim (hno q p hq hp hgt)

end PoincareConjecture.M25.Topology3D
