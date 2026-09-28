import Mathlib.Algebra.Homology.ShortComplex.ModuleCat










set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem exists_integral_shortExact_gluing
    (S : ShortComplex (ModuleCat.{u} Int)) (hS : S.ShortExact)
    (a : S.X₂) (ha : S.g a = 0) :
    ∃ b : S.X₁, S.f b = a := by
  exact (ShortComplex.moduleCat_exact_iff S).mp hS.exact a ha

theorem integral_shortExact_gluing_unique
    (S : ShortComplex (ModuleCat.{u} Int)) (hS : S.ShortExact)
    {a : S.X₂} {b₁ b₂ : S.X₁}
    (hb₁ : S.f b₁ = a) (hb₂ : S.f b₂ = a) :
    b₁ = b₂ := by
  apply hS.injective_f
  exact hb₁.trans hb₂.symm

theorem exists_unique_integral_shortExact_gluing
    (S : ShortComplex (ModuleCat.{u} Int)) (hS : S.ShortExact)
    (a : S.X₂) (ha : S.g a = 0) :
    ∃! b : S.X₁, S.f b = a := by
  obtain ⟨b, hb⟩ := exists_integral_shortExact_gluing S hS a ha
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  exact integral_shortExact_gluing_unique S hS hb' hb

end PoincareConjecture.Proofs.M02.Topology
