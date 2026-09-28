import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.FixedCoreFilling











set_option autoImplicit false

open Set

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [RegularSpace Y]





theorem exists_two_to_one_fiber_map (q : C(X, Y)) (hq : Function.Surjective q)
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
      range g = q ⁻¹' h.target := by
  classical
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
  have hRsource (x : X) : x ∈ R.source ↔ q x ≠ a ∧ q x ≠ b := by
    rw [hRs]
    simp only [mem_compl_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, not_or]
  have hregular (y : Y) (hy : y ≠ a) : h y ∈ R.target := by
    rw [hRt]
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hhne hy, hhb y⟩
  have hqinv {y : Y} (hy : y ∈ R.target) : q (R.symm y) = y :=
    (hRq (R.map_target hy)).symm.trans (R.right_inv hy)
  have hhcont : Continuous h := continuousOn_univ.mp (hhs ▸ h.continuousOn)
  let f : X → X := fun x => R.symm (h (q x))
  have hfcont : ContinuousOn f (q ⁻¹' {a})ᶜ :=
    R.symm.continuousOn.comp (hhcont.comp q.continuous).continuousOn
      (fun x hx => hregular (q x) hx)
  have hfid (x : X) (hxV : q x ∈ V) (hxa : q x ≠ a) : f x = x := by
    have hxb : q x ≠ b := fun he => hVb (he ▸ hxV)
    have hxs : x ∈ R.source := (hRsource x).mpr ⟨hxa, hxb⟩
    calc
      f x = R.symm (h (q x)) := rfl
      _ = R.symm (q x) := congrArg R.symm (hfix hxV)
      _ = R.symm (R x) := congrArg R.symm (hRq hxs).symm
      _ = x := R.left_inv hxs
  obtain ⟨C, hC, hAC, hCV⟩ :=
    OpenPartialHomeomorph.exists_closed_fiber_core q.continuous a hV ha
  have houtside {x : X} (hx : x ∉ C) : q x ≠ a :=
    fun he => hx (interior_subset (hAC he))
  have hcl : closure Cᶜ ⊆ (q ⁻¹' {a})ᶜ := by
    rw [closure_compl]
    intro x hx hxa
    exact hx (hAC hxa)
  let gfun : X → X := C.piecewise id f
  have hgcont : Continuous gfun := by
    apply continuous_piecewise _ continuous_id.continuousOn (hfcont.mono hcl)
    intro x hx
    exact (hfid x (hCV (hC.frontier_subset hx)) (fun he => hx.2 (hAC he))).symm
  let g : C(X, X) := ⟨gfun, hgcont⟩
  have hgC {x : X} (hx : x ∈ C) : g x = x := by
    exact piecewise_eq_of_mem C id f hx
  have hgout {x : X} (hx : x ∉ C) : g x = f x :=
    piecewise_eq_of_notMem C id f hx
  have hgfix : EqOn g id (q ⁻¹' V) := by
    intro x hx
    by_cases hxC : x ∈ C
    · exact hgC hxC
    · exact (hgout hxC).trans (hfid x hx (houtside hxC))
  have hgformula (x : X) (hxa : q x ≠ a) : g x = R.symm (h (q x)) := by
    by_cases hxC : x ∈ C
    · exact (hgC hxC).trans (hfid x (hCV hxC) hxa).symm
    · exact hgout hxC
  have hqg (x : X) : q (g x) = h (q x) := by
    by_cases hxa : q x = a
    · have hxV : q x ∈ V := hxa.symm ▸ ha
      exact (congrArg q (hgfix hxV)).trans (hfix hxV).symm
    · rw [hgformula x hxa]
      exact hqinv (hregular (q x) hxa)
  have hgfib (x y : X) : g x = g y ↔ x = y ∨ (q x = b ∧ q y = b) := by
    constructor
    · intro he
      have hqxy : q x = q y := h.injOn (hhsmem _) (hhsmem _)
        ((hqg x).symm.trans ((congrArg q he).trans (hqg y)))
      rcases (hfib x y).mp hqxy with hxy | hA | hB
      · exact Or.inl hxy
      · have hxV : q x ∈ V := hA.1.symm ▸ ha
        have hyV : q y ∈ V := hA.2.symm ▸ ha
        exact Or.inl ((hgfix hxV).symm.trans (he.trans (hgfix hyV)))
      · exact Or.inr hB
    · rintro (rfl | ⟨hxb, hyb⟩)
      · rfl
      · rw [hgformula x (by simpa only [hxb] using hab.symm),
          hgformula y (by simpa only [hyb] using hab.symm), hxb, hyb]
  have hgrange : range g = q ⁻¹' h.target := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change q (g x) ∈ h.target
      rw [hqg]
      exact h.map_source (hhsmem _)
    · intro hy
      change q y ∈ h.target at hy
      by_cases hya : q y = a
      · have hyV : q y ∈ V := hya.symm ▸ ha
        exact ⟨y, hgfix hyV⟩
      · obtain ⟨x, hx⟩ := hq (h.symm (q y))
        have hhx : h (q x) = q y := by rw [hx, h.right_inv hy]
        have hxa : q x ≠ a := by
          intro he
          rw [he, hha] at hhx
          exact hya hhx.symm
        have hyb : q y ≠ b := fun he => hb (he ▸ hy)
        have hys : y ∈ R.source := (hRsource y).mpr ⟨hya, hyb⟩
        refine ⟨x, ?_⟩
        rw [hgformula x hxa, hhx, ← hRq hys, R.left_inv hys]
  let c := R.symm (h b)
  have hqc : q c = h b := hqinv (hregular b hab.symm)
  have hqca : q c ≠ a := by rw [hqc]; exact hhne hab.symm
  have hqcb : q c ≠ b := by rw [hqc]; exact hhb b
  exact ⟨g, c, hqc, hqca, hqcb,
    hgfix, hgformula, hqg, hgfib, hgrange⟩

end ContinuousMap
