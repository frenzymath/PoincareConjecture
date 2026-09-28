import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.TwoToOneOpenImage
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.RegularQuotientChart
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.ChartCompactBallPair
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.CofinalFiberBallPairs

set_option autoImplicit false

open Set Topology

namespace ContinuousMap

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [Infinite E] [TopologicalSpace X] [T2Space X] [RegularSpace X]
  [TopologicalSpace Y] [RegularSpace Y] [T1Space Y]

theorem exists_second_fiber_ballPair_subset (q : C(X, Y)) (hq : IsQuotientMap q)
    (a b : Y) (hab : a ≠ b)
    (hfib : ∀ x y, q x = q y ↔ x = y ∨
      (q x = a ∧ q y = a) ∨ (q x = b ∧ q y = b))
    (hA : IsCompact (q ⁻¹' {a})) (hB : IsCompact (q ⁻¹' {b}))
    (C : OpenPartialHomeomorph X E) (hCs : C.source = univ) (hCt : C.target = univ)
    (D : OpenPartialHomeomorph Y E) (hDs : D.source = univ) (hDt : D.target = univ)
    {U : Set X} (hU : IsOpen U) (hBU : q ⁻¹' {b} ⊆ U) :
    ∃ K : Set X, IsCompact K ∧ q ⁻¹' {b} ⊆ interior K ∧ K ⊆ U ∧
      IsUnitBallPair E K (frontier K) := by
  obtain ⟨Q, hQ, hABQ, _, hQpair⟩ := C.exists_compact_ballPair_enclosing hCt
    (hA.union hB) (fun x _ => hCs.symm ▸ mem_univ x)
  have hAQ : q ⁻¹' {a} ⊆ interior Q := fun x hx => hABQ (Or.inl hx)
  have hBQ : q ⁻¹' {b} ⊆ interior Q := fun x hx => hABQ (Or.inr hx)
  have hsat : q ⁻¹' (q '' interior Q) = interior Q := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      rcases (hfib x y).mp he.symm with hxy | hAx | hBx
      · exact hxy.symm ▸ hy
      · exact hAQ hAx.1
      · exact hBQ hBx.1
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hqI : IsOpen (q '' interior Q) :=
    hq.isOpen_image_of_saturated isOpen_interior hsat
  have haqI : a ∈ q '' interior Q := by
    obtain ⟨x, hx⟩ := hq.surjective a
    exact ⟨x, hAQ hx, hx⟩
  have hDsmem (y : Y) : y ∈ D.source := hDs.symm ▸ mem_univ y
  obtain ⟨h, hhs, hht, V, hV, haV, hfix⟩ := D.exists_compression_in_chart hDt
    (hDsmem a) (hqI.sdiff isClosed_singleton) ⟨haqI, hab⟩
  have hhs' : h.source = univ := hhs.trans hDs
  have hb : b ∉ h.target := fun hb => (hht hb).2 rfl
  have hT : IsOpen (({a, b} : Set Y)ᶜ) :=
    ((Set.finite_singleton b).insert a).isClosed.isOpen_compl
  have hTne : (({a, b} : Set Y)ᶜ).Nonempty := by
    obtain ⟨z, hz⟩ := ((Set.finite_singleton (D b)).insert (D a)).exists_notMem
    have hzt : z ∈ D.target := hDt.symm ▸ mem_univ z
    refine ⟨D.symm z, ?_⟩
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro he
      have hv : z = D a := (D.right_inv hzt).symm.trans (congrArg D he)
      exact hz (by simp [hv])
    · intro he
      have hv : z = D b := (D.right_inv hzt).symm.trans (congrArg D he)
      exact hz (by simp [hv])
  have hinj : InjOn q (q ⁻¹' ({a, b} : Set Y)ᶜ) := by
    intro x hx y _ he
    rcases (hfib x y).mp he with hxy | hAx | hBx
    · exact hxy
    · exact False.elim (hx (by simp [hAx.1]))
    · exact False.elim (hx (by simp [hBx.1]))
  obtain ⟨R, hRs, hRt, hRq⟩ := hq.exists_regular_chart hT hTne hinj
  have hRs' : R.source = (q ⁻¹' ({a, b} : Set Y))ᶜ := by
    simpa only [preimage_compl] using hRs
  have hRq' : EqOn R q R.source := by
    intro x hx
    exact hRq (hRs ▸ hx)
  obtain ⟨g, c, hc, hpre, hgfib, _, ⟨Rg, hRgs, hRgt, hRgg⟩, hgopen⟩ :=
    q.exists_two_to_one_open_regular_map hq a b hab hfib R hRs' hRt hRq'
      h hhs' hb hV haV hfix
  have hfcQ : g ⁻¹' {c} ⊆ interior Q := by simpa only [hpre] using hBQ
  have hfcU : g ⁻¹' {c} ⊆ U := by simpa only [hpre] using hBU
  obtain ⟨K, hK, hfK, hKU, hKpair⟩ := g.exists_fiber_ballPair_subset c hc hgfib
    C hCs hCt Rg hRgs hRgt hRgg hQ hQpair hfcQ
      (hgopen (interior Q) isOpen_interior hAQ hBQ) hU hfcU
  exact ⟨K, hK, hpre ▸ hfK, hKU, hKpair⟩

end ContinuousMap
