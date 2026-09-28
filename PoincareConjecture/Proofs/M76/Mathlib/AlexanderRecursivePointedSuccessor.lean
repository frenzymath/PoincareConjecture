import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedTime
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedZero











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem AlexanderCollarSlab.exists_pointed_successor_time
    {S s s' b d : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hinter : s ∩ s' ⊆ b) (hqs : q ∈ s) (hqb : q ∈ b)
    (hcap : d ∩ S = b) (hbd : b ⊆ d) (hd : d ⊆ {x | A x = 0})
    (N Ks Kd Kb : SimplicialComplex ℝ E)
    (hN : N.faces.Finite) (hKs : Ks.faces.Finite) (hKss : Ks.space = s)
    (hKd : Kd.faces.Finite) (hKds : Kd.space = d)
    (hKb : Kb.faces.Finite) (hKbs : Kb.space = b)
    (hB : S ∩ {x | A x = 0} = b ∪ N.space) (hdN : d ∩ N.space ⊆ {q})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    {g : E → ℝ} (hg : FinitePiecewiseAffineOn g M.collar)
    (hgN : ∀ x ∈ N.space, g x = 0) (hgq : g q = 0)
    (hgR : ∀ x ∈ M.residual, g x = 0)
    (v : E) (hv : A.linear v = 1) {ε : ℝ} (hε : 0 < ε)
    (H : Icc (-ε) ε → E ≃ₜ E)
    (hglobal : ∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
      FinitePiecewiseAffineOn (H t : E → E) L.space)
    (hformula : ∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v)
    (hall : ∀ t : Icc (-ε) ε, 0 < (t : ℝ) →
      (∀ x, A x ≤ A (H t x)) ∧
      (∀ x ∈ s, A x < 0 → H t x = x) ∧
      (∀ x, β ≤ A x → H t x = x) ∧
      ((H t '' (s ∪ d)) ∩ {x | A x = 0} =
        (((s ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q}))) :
    ∃ t : Icc (-ε) ε, 0 < (t : ℝ) ∧
      Nonempty (AlexanderCollarSlab (H t '' (s ∪ d)) A q β) := by
  apply M.exists_selected_successor_time hs hs' hunion hinter hqs hcap hbd hd
    N Ks Kd Kb hN hKs hKss hKd hKds hKb hKbs hB hdN hselected hg hgN hgq
    hgR v hv hε H hglobal hformula
  intro t ht
  obtain ⟨hraise, hneg, hhigh, hzero⟩ := hall t ht
  exact ⟨hraise, hneg, hhigh, hzero.trans (M.selected_zero_section_eq
    (subset_union_left.trans hunion.subset) hB hcap hbd hdN (hbd hqb))⟩

end Geometry
