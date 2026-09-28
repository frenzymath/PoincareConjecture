import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.TwoToOneRegularChart
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.RegularQuotient











set_option autoImplicit false

open Set Topology

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [RegularSpace Y] [T1Space Y]




theorem exists_two_to_one_open_regular_map (q : C(X, Y)) (hq : IsQuotientMap q)
    (a b : Y) (hab : a ≠ b)
    (hfib : ∀ x y, q x = q y ↔ x = y ∨
      (q x = a ∧ q y = a) ∨ (q x = b ∧ q y = b))
    (R : OpenPartialHomeomorph X Y)
    (hRs : R.source = (q ⁻¹' ({a, b} : Set Y))ᶜ) (hRt : R.target = ({a, b} : Set Y)ᶜ)
    (hRq : EqOn R q R.source) (h : OpenPartialHomeomorph Y Y)
    (hhs : h.source = univ) (hb : b ∉ h.target)
    {V : Set Y} (hV : IsOpen V) (ha : a ∈ V) (hfix : EqOn h id V) :
    ∃ (g : C(X, X)) (c : X), c ∈ range g ∧
      g ⁻¹' {c} = q ⁻¹' {b} ∧
      (∀ x y, g x = g y ↔ x = y ∨ (g x = c ∧ g y = c)) ∧
      range g = q ⁻¹' h.target ∧
      (∃ Rg : OpenPartialHomeomorph X X,
        Rg.source = (g ⁻¹' {c})ᶜ ∧ Rg.target = range g \ {c} ∧
        EqOn Rg g Rg.source) ∧
      ∀ U : Set X, IsOpen U → q ⁻¹' {a} ⊆ U → q ⁻¹' {b} ⊆ U →
        IsOpen (g '' U) := by
  obtain ⟨g, c, hqc, hqca, hqcb, _, _, hqg, hgfib, hgrange,
      Rg, hRgs, hRgt, hRgg⟩ :=
    q.exists_two_to_one_fiber_regular_map hq.surjective a b hab hfib
      R hRs hRt hRq h hhs hb hV ha hfix
  have hhsmem (y : Y) : y ∈ h.source := hhs.symm ▸ mem_univ y
  have hgcb (x : X) : g x = c ↔ q x = b := by
    constructor
    · intro hx
      exact h.injOn (hhsmem _) (hhsmem _)
        ((hqg x).symm.trans ((congrArg q hx).trans hqc))
    · intro hx
      have he : q (g x) = q c := by rw [hqg, hx, hqc]
      rcases (hfib (g x) c).mp he with hxy | hA | hB
      · exact hxy
      · exact False.elim (hqca hA.2)
      · exact False.elim (hqcb hB.2)
  have hpre : g ⁻¹' {c} = q ⁻¹' {b} := by
    ext x
    exact hgcb x
  have hcrange : c ∈ range g := by
    obtain ⟨x, hx⟩ := hq.surjective b
    exact ⟨x, (hgcb x).mpr hx⟩
  refine ⟨g, c, hcrange, hpre, ?_, hgrange, ?_, ?_⟩
  · intro x y
    rw [hgfib, hgcb x, hgcb y]
  · exact ⟨Rg, hRgs.trans (congrArg compl hpre).symm,
      hRgt.trans (congrArg (fun T : Set X => T \ {c}) hgrange).symm, hRgg⟩
  · intro U hU hAU hBU
    have hsat : q ⁻¹' (q '' U) = U := by
      ext x
      constructor
      · rintro ⟨y, hy, he⟩
        rcases (hfib x y).mp he.symm with hxy | hA | hB
        · exact hxy.symm ▸ hy
        · exact hAU hA.1
        · exact hBU hB.1
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hqU : IsOpen (q '' U) := hq.isOpen_image_of_saturated hU hsat
    have hgU : g '' U = q ⁻¹' (h '' (q '' U)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨q x, ⟨x, hx, rfl⟩, (hqg x).symm⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, he⟩
        have hyt : q y ∈ h.target := he ▸ h.map_source (hhsmem (q x))
        have hyr : y ∈ range g := by rw [hgrange]; exact hyt
        obtain ⟨w, hw⟩ := hyr
        have hqwx : q w = q x := by
          apply h.injOn (hhsmem _) (hhsmem _)
          exact (hqg w).symm.trans ((congrArg q hw).trans he.symm)
        have hwU : w ∈ U := by
          have hm : w ∈ q ⁻¹' (q '' U) := ⟨x, hx, hqwx.symm⟩
          rwa [hsat] at hm
        exact ⟨w, hwU, hw⟩
    rw [hgU]
    exact (h.isOpen_image_of_subset_source hqU (fun y _ => hhsmem y)).preimage q.continuous

end ContinuousMap
