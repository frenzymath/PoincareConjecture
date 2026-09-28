import PoincareConjecture.Proofs.M76.Mathlib.CompactPLRelativeRegularLevels

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

theorem relative_superlevel_frontier_charts
    {M E ι : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    {w : M → ℝ} (hw : Continuous w) {R : Set M} (hR : IsClosed R) {t : ℝ}
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))
    (hlevel : ∀ x : M, w x = t →
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, ell (B y) = w y)
    (hcorner : ∀ x ∈ frontier R, w x = t →
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, (y ∈ R ∧ t ≤ w y) ↔ 0 ≤ ell (B y)) :
    ∀ x ∈ frontier {y | y ∈ R ∧ t ≤ w y},
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, (y ∈ R ∧ t ≤ w y) ↔ 0 ≤ ell (B y) := by
  have hrestrict (B : OpenPartialHomeomorph M E)
      (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) (U : Set M) :
      ∀ i, (e i).symm.trans (B.restr U) ∈ piecewiseAffineGroupoid E := by
    intro i
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hB i)).mono
      ((e i).symm.trans (B.restr U)).open_source (fun z hz => ⟨hz.1, hz.2.1⟩)
  have hclosed : IsClosed {y | y ∈ R ∧ t ≤ w y} :=
    hR.inter (isClosed_le continuous_const hw)
  intro x hx
  have hxN : x ∈ R ∧ t ≤ w x := hclosed.closure_subset hx.1
  by_cases hxt : w x = t
  · by_cases hxold : x ∈ frontier R
    · exact hcorner x hxold hxt
    · have hxint : x ∈ interior R := by
        by_contra hxnot
        exact hxold ⟨subset_closure hxN.1, hxnot⟩
      obtain ⟨ell, v, B, hellv, hxB, hBPL, hheight⟩ := hlevel x hxt
      let ell0 := ell - ContinuousAffineMap.const ℝ E t
      let C := B.restr (interior R)
      have hxC : x ∈ C.source := ⟨hxB, by simpa only [interior_interior] using hxint⟩
      refine ⟨ell0, v, C, ?_, hxC, ?_, hrestrict B hBPL _, ?_⟩
      · simpa only [ell0, ContinuousAffineMap.sub_contLinear,
          ContinuousAffineMap.const_contLinear, sub_zero] using hellv
      · change ell (B x) - t = 0
        rw [hheight x hxB, hxt, sub_self]
      · intro y hy
        have hyR : y ∈ R := interior_subset (interior_subset hy.2)
        change (y ∈ R ∧ t ≤ w y) ↔ 0 ≤ ell (B y) - t
        rw [hheight y hy.1]
        simp only [hyR, true_and, sub_nonneg]
  · have hstrict : t < w x := lt_of_le_of_ne hxN.2 (Ne.symm hxt)
    let U : Set M := {y | t < w y}
    have hU : IsOpen U := isOpen_lt continuous_const hw
    have hxold : x ∈ frontier R := by
      refine ⟨subset_closure hxN.1, ?_⟩
      intro hxint
      apply hx.2
      exact interior_maximal
        (show interior R ∩ U ⊆ {y | y ∈ R ∧ t ≤ w y} from
          fun y hy => ⟨interior_subset hy.1, (show t < w y from hy.2).le⟩)
        (isOpen_interior.inter hU) ⟨hxint, hstrict⟩
    obtain ⟨ell, v, B, hellv, hxB, hellx, hBPL, hBR⟩ := hboundary x hxold
    let C := B.restr U
    have hxC : x ∈ C.source := ⟨hxB, hU.interior_eq.symm ▸ hstrict⟩
    refine ⟨ell, v, C, hellv, hxC, hellx, hrestrict B hBPL U, ?_⟩
    intro y hy
    have hyU : y ∈ U := interior_subset hy.2
    have hystrict : t < w y := hyU
    change (y ∈ R ∧ t ≤ w y) ↔ 0 ≤ ell (B y)
    simp only [hystrict.le, and_true, hBR y hy.1]

end OpenPartialHomeomorph
