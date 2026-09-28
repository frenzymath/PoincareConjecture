import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.SpanningArcDisk
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

theorem exists_unique_spanning_interval_of_one_marked_point
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (pieces : κ → Set E) (Q₀ Q₁ : Set E) (a : E)
    (hQ : Disjoint Q₀ Q₁)
    (hdis : Pairwise (fun i j ↦ Disjoint (pieces i) (pieces j)))
    (hfirst : (⋃ i, pieces i) ∩ Q₀ = {a})
    (hmodels : ∀ i, IsFinitePLBallPair ℝ (pieces i) (pieces i ∩ (Q₀ ∪ Q₁)) ∨
      ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
        P.HasSimplicialEdges ∧ P.boundary ℝ = pieces i ∧ Disjoint (pieces i) (Q₀ ∪ Q₁)) :
    ∃ (i : κ) (b : E), a ∈ Q₀ ∧ b ∈ Q₁ ∧ a ≠ b ∧
      IsFinitePLBallPair ℝ (pieces i) {a, b} ∧
      pieces i ∩ (Q₀ ∪ Q₁) = {a, b} ∧
      pieces i ∩ Q₀ = {a} ∧ pieces i ∩ Q₁ = {b} ∧
      (∀ j, (pieces j ∩ Q₀).Nonempty ↔ j = i) ∧
      ∀ j, j ≠ i → Disjoint (pieces j) Q₀ ∧
        pieces j ∩ (Q₀ ∪ Q₁) = pieces j ∩ Q₁ ∧
        (IsFinitePLBallPair ℝ (pieces j) (pieces j ∩ Q₁) ∨
          ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
            P.HasSimplicialEdges ∧ P.boundary ℝ = pieces j ∧ Disjoint (pieces j) (Q₀ ∪ Q₁)) := by
  have ha := hfirst.symm.subset (mem_singleton a)
  obtain ⟨i, hai⟩ := mem_iUnion.mp ha.1
  have hball : IsFinitePLBallPair ℝ (pieces i) (pieces i ∩ (Q₀ ∪ Q₁)) := by
    rcases hmodels i with hi | ⟨_, _, _, _, _, hd⟩
    · exact hi
    · exact (disjoint_left.mp hd hai (Or.inl ha.2)).elim
  obtain ⟨u, v, huv, hends⟩ := hball.exists_boundary_eq_pair
  have hapair : a ∈ ({u, v} : Set E) := hends.subset ⟨hai, Or.inl ha.2⟩
  have hother : ∃ b, a ≠ b ∧ pieces i ∩ (Q₀ ∪ Q₁) = {a, b} := by
    rcases hapair with rfl | h
    · exact ⟨v, huv, hends⟩
    · have hav : a = v := h
      subst a
      exact ⟨u, huv.symm, hends.trans (pair_comm u v)⟩
  obtain ⟨b, hab, hpair⟩ := hother
  have hbQ : b ∈ Q₁ := by
    have hb := hpair.symm.subset (show b ∈ ({a, b} : Set E) from Or.inr rfl)
    rcases hb.2 with hb₀ | hb₁
    · have hba : b = a := hfirst.subset ⟨mem_iUnion.mpr ⟨i, hb.1⟩, hb₀⟩
      exact (hab hba.symm).elim
    · exact hb₁
  have hothers (j : κ) (hji : j ≠ i) : Disjoint (pieces j) Q₀ := by
    apply disjoint_left.mpr
    intro x hx hxQ
    have hxa : x = a := hfirst.subset ⟨mem_iUnion.mpr ⟨j, hx⟩, hxQ⟩
    exact disjoint_left.mp (hdis hji) hx (hxa.symm ▸ hai)
  have hfirsti : pieces i ∩ Q₀ = {a} := by
    apply subset_antisymm
    · exact fun x hx ↦ hfirst.subset ⟨mem_iUnion.mpr ⟨i, hx.1⟩, hx.2⟩
    · rintro x rfl
      exact ⟨hai, ha.2⟩
  have hlasti : pieces i ∩ Q₁ = {b} := by
    apply subset_antisymm
    · intro x hx
      rcases hpair.subset ⟨hx.1, Or.inr hx.2⟩ with hxa | hxb
      · exact (disjoint_left.mp hQ (hxa.symm ▸ ha.2) hx.2).elim
      · exact hxb
    · rintro x rfl
      exact ⟨(hpair.symm.subset (Or.inr rfl)).1, hbQ⟩
  refine ⟨i, b, ha.2, hbQ, hab, hpair ▸ hball, hpair, hfirsti, hlasti, ?_, ?_⟩
  · intro j
    constructor
    · rintro ⟨x, hx, hxQ⟩
      by_contra hji
      exact disjoint_left.mp (hothers j hji) hx hxQ
    · rintro rfl
      exact ⟨a, hai, ha.2⟩
  · intro j hji
    have heq : pieces j ∩ (Q₀ ∪ Q₁) = pieces j ∩ Q₁ := by
      ext x
      constructor
      · rintro ⟨hx, hxQ | hxQ⟩
        · exact (disjoint_left.mp (hothers j hji) hx hxQ).elim
        · exact ⟨hx, hxQ⟩
      · rintro ⟨hx, hxQ⟩
        exact ⟨hx, Or.inr hxQ⟩
    refine ⟨hothers j hji, heq, ?_⟩
    rcases hmodels j with hj | hj
    · exact Or.inl (heq ▸ hj)
    · exact Or.inr hj

end PoincareConjecture.M76.Dehn.Annuli
