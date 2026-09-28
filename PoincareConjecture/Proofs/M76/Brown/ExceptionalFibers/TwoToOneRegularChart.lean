import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.TwoToOneFiberMap
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.PartialFixedCoreFilling











set_option autoImplicit false

open Set

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [RegularSpace Y] [T1Space Y]




theorem exists_two_to_one_fiber_regular_map (q : C(X, Y)) (hq : Function.Surjective q)
    (a b : Y) (hab : a ≠ b)
    (hfib : ∀ x y, q x = q y ↔ x = y ∨
      (q x = a ∧ q y = a) ∨ (q x = b ∧ q y = b))
    (R : OpenPartialHomeomorph X Y)
    (hRs : R.source = (q ⁻¹' ({a, b} : Set Y))ᶜ) (hRt : R.target = ({a, b} : Set Y)ᶜ)
    (hRq : EqOn R q R.source) (h : OpenPartialHomeomorph Y Y)
    (hhs : h.source = univ) (hb : b ∉ h.target)
    {V : Set Y} (hV : IsOpen V) (ha : a ∈ V) (hfix : EqOn h id V) :
    ∃ (g : C(X, X)) (c : X),
      q c = h b ∧ q c ≠ a ∧ q c ≠ b ∧
      EqOn g id (q ⁻¹' V) ∧
      (∀ x, q x ≠ a → g x = R.symm (h (q x))) ∧
      (∀ x, q (g x) = h (q x)) ∧
      (∀ x y, g x = g y ↔ x = y ∨ (q x = b ∧ q y = b)) ∧
      range g = q ⁻¹' h.target ∧
      ∃ Rg : OpenPartialHomeomorph X X,
        Rg.source = (q ⁻¹' {b})ᶜ ∧ Rg.target = (q ⁻¹' h.target) \ {c} ∧
        EqOn Rg g Rg.source := by
  obtain ⟨g, c, hqc, hqca, hqcb, hgfix, hgformula, hqg, hgfib, hgrange⟩ :=
    q.exists_two_to_one_fiber_map hq a b hab hfib R hRs hRt hRq h hhs hb hV ha hfix
  have hhsmem (y : Y) : y ∈ h.source := hhs.symm ▸ mem_univ y
  have hha : h a = a := hfix ha
  have hhne {y : Y} (hy : y ≠ a) : h y ≠ a := by
    intro he
    exact hy (h.injOn (hhsmem y) (hhsmem a) (he.trans hha.symm))
  have hhb (y : Y) : h y ≠ b := fun he => hb (he ▸ h.map_source (hhsmem y))
  have hVb : b ∉ V := by
    intro hbV
    have hm := h.map_source (hhsmem b)
    have he : h b = b := hfix hbV
    rw [he] at hm
    exact hb hm
  have hhbV : h b ∉ V := by
    intro hhV
    have he : h (h b) = h b := hfix hhV
    exact hhb b (h.injOn (hhsmem _) (hhsmem _) he)
  have hRsource (x : X) : x ∈ R.source ↔ q x ≠ a ∧ q x ≠ b := by
    rw [hRs]
    simp only [mem_compl_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, not_or]
  have hRtarget (y : Y) : y ∈ R.target ↔ y ≠ a ∧ y ≠ b := by
    rw [hRt]
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  have hcR : c ∈ R.source := (hRsource c).mpr ⟨hqca, hqcb⟩
  have hRc : R c = h b := (hRq hcR).trans hqc
  let e := R.trans (h.trans R.symm)
  have hes : e.source = (q ⁻¹' {b})ᶜ \ (q ⁻¹' {a}) := by
    ext x
    change (x ∈ R.source ∧ R x ∈ h.source ∧ h (R x) ∈ R.target) ↔
      (q x ≠ b ∧ q x ≠ a)
    constructor
    · intro hx
      exact (hRsource x).mp hx.1 |>.symm
    · rintro ⟨hxb, hxa⟩
      have hxs : x ∈ R.source := (hRsource x).mpr ⟨hxa, hxb⟩
      refine ⟨hxs, hhsmem _, (hRtarget _).mpr ⟨?_, hhb _⟩⟩
      exact hhne ((hRtarget _).mp (R.map_source hxs)).1
  have het : e.target = ((q ⁻¹' h.target) \ {c}) \ (q ⁻¹' {a}) := by
    ext y
    change ((y ∈ R.source ∧ R y ∈ h.target) ∧ h.symm (R y) ∈ R.target) ↔
      ((q y ∈ h.target ∧ y ≠ c) ∧ q y ≠ a)
    constructor
    · rintro ⟨⟨hys, hyt⟩, hi⟩
      refine ⟨⟨(hRq hys) ▸ hyt, ?_⟩, ((hRsource y).mp hys).1⟩
      intro hyc
      have hineq := ((hRtarget _).mp hi).2
      rw [hyc, hRc, h.left_inv (hhsmem b)] at hineq
      exact hineq rfl
    · rintro ⟨⟨hyt, hyc⟩, hya⟩
      have hyb : q y ≠ b := fun he => hb (he ▸ hyt)
      have hys : y ∈ R.source := (hRsource y).mpr ⟨hya, hyb⟩
      have hyr : R y ∈ h.target := (hRq hys).symm ▸ hyt
      refine ⟨⟨hys, hyr⟩, (hRtarget _).mpr ⟨?_, ?_⟩⟩
      · intro he
        have hv := congrArg h he
        rw [h.right_inv hyr, hha] at hv
        exact ((hRtarget _).mp (R.map_source hys)).1 hv
      · intro he
        have hv : R y = h b := (h.right_inv hyr).symm.trans (congrArg h he)
        exact hyc (R.injOn hys hcR (hv.trans hRc.symm))
  have hefix : EqOn e id ((q ⁻¹' V) \ (q ⁻¹' {a})) := by
    intro x hx
    have hxb : q x ≠ b := fun he => hVb (he ▸ hx.1)
    have hxs : x ∈ R.source := (hRsource x).mpr ⟨hx.2, hxb⟩
    have hxV : R x ∈ V := (hRq hxs).symm ▸ hx.1
    change R.symm (h (R x)) = x
    calc
      R.symm (h (R x)) = R.symm (R x) := congrArg R.symm (hfix hxV)
      _ = x := R.left_inv hxs
  obtain ⟨C, hC, hAC, hCV⟩ :=
    OpenPartialHomeomorph.exists_closed_fiber_core q.continuous a hV ha
  have hCU : C ⊆ (q ⁻¹' {b})ᶜ := by
    intro x hx hxb
    exact hVb (hxb ▸ hCV hx)
  have hCT : C ⊆ (q ⁻¹' h.target) \ {c} := by
    intro x hx
    have hxV := hCV hx
    refine ⟨?_, ?_⟩
    · change q x ∈ h.target
      have hm := h.map_source (hhsmem (q x))
      simpa only [hfix hxV, id_eq] using hm
    · intro hxc
      have hcV : q c ∈ V := hxc ▸ hxV
      exact hhbV (hqc ▸ hcV)
  have hU : IsOpen (q ⁻¹' {b})ᶜ :=
    (isClosed_singleton.preimage q.continuous).isOpen_compl
  have hfixC : EqOn e id (C \ (q ⁻¹' {a})) := by
    intro x hx
    exact hefix ⟨hCV hx.1, hx.2⟩
  obtain ⟨Rg, hRgs, hRgt, hRgC, hRge⟩ := e.exists_fill_fixed_core_on_open hU hes het
    hC hAC hCU hCT hfixC
  refine ⟨g, c, hqc, hqca, hqcb, hgfix, hgformula, hqg, hgfib, hgrange,
    Rg, hRgs, hRgt, ?_⟩
  intro x hx
  have hxb : q x ≠ b := by
    have hxm : x ∈ (q ⁻¹' {b})ᶜ := by simpa only [hRgs] using hx
    exact hxm
  by_cases hxC : x ∈ C
  · exact (hRgC hxC).trans (hgfix (hCV hxC)).symm
  · have hxa : q x ≠ a := fun he => hxC (interior_subset (hAC he))
    have hxs : x ∈ R.source := (hRsource x).mpr ⟨hxa, hxb⟩
    calc
      Rg x = e x := hRge hxC
      _ = R.symm (h (q x)) := by change R.symm (h (R x)) = _; rw [hRq hxs]
      _ = g x := (hgformula x hxa).symm

end ContinuousMap
