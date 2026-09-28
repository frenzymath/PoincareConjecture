import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorFiniteJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem weakSchwartzJet_unique {q p : List (Fin n) → L2} {s : ℕ}
    (hq : IsWeakSchwartzJet q s) (hp : IsWeakSchwartzJet p s) (h0 : q [] = p [])
    (w : List (Fin n)) (hw : w.length ≤ s) : q w = p w :=
  hq.eq_of_nil_eq hp h0 w hw

theorem exists_coherent_weakJet (u : L2) (hu : ∀ s, HasFiniteWeakJet u s) :
    ∃ q : List (Fin n) → L2, q [] = u ∧ ∀ s, IsWeakSchwartzJet q s := by
  choose Q hQ0 hQ using hu
  let q := fun w : List (Fin n) => Q (w.length + 1) w
  have hcompat (r s : ℕ) (w : List (Fin n)) (hr : w.length ≤ r) (hs : w.length ≤ s) :
      Q r w = Q s w :=
    weakSchwartzJet_unique ((hQ r).mono hr) ((hQ s).mono hs)
      ((hQ0 r).trans (hQ0 s).symm) w le_rfl
  refine ⟨q, hQ0 1, ?_⟩
  intro s w _hw i
  have hd := hQ (w.length + 2) w (by omega) i
  change HasWeakSchwartzDerivative (Q (w.length + 1) w)
    (Q ((i :: w).length + 1) (i :: w)) (EuclideanSpace.single i (1 : ℝ))
  simpa only [List.length_cons, Nat.add_assoc,
    hcompat (w.length + 2) (w.length + 1) w (by omega) (by omega)] using hd

theorem weakSchwartzJet_sub {q p : List (Fin n) → L2} {s : ℕ}
    (hq : IsWeakSchwartzJet q s) (hp : IsWeakSchwartzJet p s) :
    IsWeakSchwartzJet (fun w => q w - p w) s :=
  fun w hw i => weakSchwartzDerivative_sub (hq w hw i) (hp w hw i)

theorem exists_coherent_interior_jet {K : Set V} (u : dirichletForm K)
    (hu : ∀ s, HasInteriorWeakJets K u s)
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K) :
    ∃ q : List (Fin n) → L2,
      q [] = localizedDirichletValue K χ u ∧
      (∀ i, q [i] = localizedDirichletPartial K χ u i) ∧
      ∀ s, IsWeakSchwartzJet q s := by
  obtain ⟨q, hq0, hq⟩ := exists_coherent_weakJet
    (localizedDirichletValue K χ u) (fun s => hu s χ hχ hχK)
  refine ⟨q, hq0, ?_, hq⟩
  intro i
  have hd := hq 1 [] (by simp) i
  rw [hq0] at hd
  exact hd.unique (localizedDirichletPartial_weak K χ u i)

end PoincareConjecture.M35.Uniqueness.Heat
