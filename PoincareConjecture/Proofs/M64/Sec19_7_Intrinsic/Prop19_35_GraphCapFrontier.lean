import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GraphCap













noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture





theorem m64Intrinsic_graph_cap_frontier_subset
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) {h : ℝ → ℝ} {X : Set ℝ} {a b d : ℝ}
    (hX : IsOpen X) (hh : ContDiffOn ℝ ∞ h X) (hI : Icc a b ⊆ X)
    {K : Set AnnulusCoordinates}
    (hgraph : ∀ s ∈ Icc a b, L.symm (s, h s) ∈ K)
    (hcompact : IsCompact
      (L.symm '' {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ h q.1 ≤ q.2 ∧ q.2 ≤ d})) :
    frontier (L.symm '' {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ h q.1 ≤ q.2 ∧ q.2 ≤ d}) ⊆
      K ∪ {z | (L z).1 = a ∨ (L z).1 = b ∨ (L z).2 = d} := by
  intro z hz
  have hzmem := hcompact.isClosed.closure_eq ▸ frontier_subset_closure hz
  obtain ⟨q, hq, rfl⟩ := hzmem
  simp only [mem_union, mem_ofPred_eq, L.apply_symm_apply]
  by_cases hlow : q.2 = h q.1
  · left
    convert hgraph q.1 hq.1 using 1
    exact congrArg L.symm (Prod.ext rfl hlow)
  by_cases ha : q.1 = a
  · exact Or.inr (Or.inl ha)
  by_cases hb : q.1 = b
  · exact Or.inr (Or.inr (Or.inl hb))
  by_cases hd : q.2 = d
  · exact Or.inr (Or.inr (Or.inr hd))
  have hal : a < q.1 := lt_of_le_of_ne hq.1.1 (Ne.symm ha)
  have hbr : q.1 < b := lt_of_le_of_ne hq.1.2 hb
  have hhl : h q.1 < q.2 := lt_of_le_of_ne hq.2.1 (Ne.symm hlow)
  have hdh : q.2 < d := lt_of_le_of_ne hq.2.2 hd
  have hhq : ContinuousAt h q.1 :=
    (hh q.1 (hI hq.1)).continuousWithinAt.continuousAt (hX.mem_nhds (hI hq.1))
  have hleft : ∀ᶠ w : ℝ × ℝ in 𝓝 q, a < w.1 :=
    continuousAt_const.eventually_lt continuousAt_fst hal
  have hright : ∀ᶠ w : ℝ × ℝ in 𝓝 q, w.1 < b :=
    continuousAt_fst.eventually_lt continuousAt_const hbr
  have hlower : ∀ᶠ w : ℝ × ℝ in 𝓝 q, h w.1 < w.2 :=
    (hhq.comp continuousAt_fst).eventually_lt continuousAt_snd hhl
  have hupper : ∀ᶠ w : ℝ × ℝ in 𝓝 q, w.2 < d :=
    continuousAt_snd.eventually_lt continuousAt_const hdh
  have hn : {w : ℝ × ℝ | w.1 ∈ Icc a b ∧ h w.1 ≤ w.2 ∧ w.2 ≤ d} ∈ 𝓝 q := by
    filter_upwards [hleft, hright, hlower, hupper] with w hw₁ hw₂ hw₃ hw₄
    exact ⟨⟨hw₁.le, hw₂.le⟩, hw₃.le, hw₄.le⟩
  exact False.elim (hz.2 (mem_interior_iff_mem_nhds.mpr
    (L.symm.toHomeomorph.isOpenMap.image_mem_nhds hn)))





theorem m64Intrinsic_graph_cap_interface_lines
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (a b d : ℝ) :
    ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧
      {z | (L z).1 = a ∨ (L z).1 = b ∨ (L z).2 = d} =
        ⋃ l ∈ lines, {z | l z = 0} := by
  let x : AnnulusCoordinates →ₗ[ℝ] ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp L.toContinuousLinearMap).toLinearMap
  let y : AnnulusCoordinates →ₗ[ℝ] ℝ :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp L.toContinuousLinearMap).toLinearMap
  let la := x.toAffineMap - AffineMap.const ℝ AnnulusCoordinates a
  let lb := x.toAffineMap - AffineMap.const ℝ AnnulusCoordinates b
  let ld := y.toAffineMap - AffineMap.const ℝ AnnulusCoordinates d
  have hla : Function.Surjective la := by
    intro t
    refine ⟨L.symm (t + a, 0), ?_⟩
    change (L (L.symm (t + a, 0))).1 - a = t
    rw [L.apply_symm_apply]
    dsimp only
    ring
  have hlb : Function.Surjective lb := by
    intro t
    refine ⟨L.symm (t + b, 0), ?_⟩
    change (L (L.symm (t + b, 0))).1 - b = t
    rw [L.apply_symm_apply]
    dsimp only
    ring
  have hld : Function.Surjective ld := by
    intro t
    refine ⟨L.symm (0, t + d), ?_⟩
    change (L (L.symm (0, t + d))).2 - d = t
    rw [L.apply_symm_apply]
    dsimp only
    ring
  refine ⟨[la, lb, ld], ?_, ?_⟩
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact hla
    · exact hlb
    · exact hld
  · ext z
    have ha : la z = 0 ↔ (L z).1 = a := sub_eq_zero
    have hb : lb z = 0 ↔ (L z).1 = b := sub_eq_zero
    have hd : ld z = 0 ↔ (L z).2 = d := sub_eq_zero
    simp only [mem_ofPred_eq, mem_iUnion, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro hz
      rcases hz with hz | hz | hz
      · exact ⟨la, Or.inl rfl, ha.mpr hz⟩
      · exact ⟨lb, Or.inr (Or.inl rfl), hb.mpr hz⟩
      · exact ⟨ld, Or.inr (Or.inr rfl), hd.mpr hz⟩
    · rintro ⟨l, hl, hz⟩
      rcases hl with rfl | rfl | rfl
      · exact Or.inl (ha.mp hz)
      · exact Or.inr (Or.inl (hb.mp hz))
      · exact Or.inr (Or.inr (hd.mp hz))

end PoincareConjecture
