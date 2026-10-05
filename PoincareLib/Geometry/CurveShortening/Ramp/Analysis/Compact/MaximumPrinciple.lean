import PoincareLib.Analysis.Parabolic.CompactMaximum

/-!
# Compact comparison with derivatives only at interior times

Reuse M05's compact maximum comparison, the scalar argument in Morgan--Tian
Theorems 4.7-4.8, p. 66, on each smaller closed slab. Continuity supplies
the final endpoint. This is the time-regularity form needed by Corollary
19.13 and corrected Lemma 19.14, MT2007 pp. 446-447 and the 2015 correction
pp. 8-9. Spatial differential inequalities enter through the contact bound.
-/

set_option autoImplicit false

open Set

namespace Poincare.Parabolic

/-- The compact maximum comparison needs no derivative at either endpoint
when the family is jointly continuous on the closed slab. This adapts M05
for Corollary 19.13 and corrected Lemma 19.14, MT2007 pp. 446-447. -/
theorem nonpos_of_deriv_le_mul_at_max_interior
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {F V : A → ℝ → ℝ} {K a b : ℝ} (hab : a < b)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hderiv : ∀ q t, t ∈ Ioo a b → HasDerivAt (F q) (V q t) t)
    (hmax : ∀ q t, t ∈ Ioo a b → 0 < F q t →
      (∀ p, F p t ≤ F q t) → V q t ≤ K * F q t)
    (hinit : ∀ q, F q a ≤ 0) :
    ∀ q t, t ∈ Icc a b → F q t ≤ 0 := by
  have hbefore : ∀ q t, t ∈ Ico a b → F q t ≤ 0 := by
    intro q t ht
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2.le
    have h := nonpos_of_deriv_le_mul_at_max
      (hF.mono (Set.prod_mono Subset.rfl hsub))
      (fun p s hs => (hderiv p s ⟨hs.1, hs.2.trans_lt ht.2⟩).hasDerivWithinAt)
      (fun p s hs => hmax p s ⟨hs.1, hs.2.trans_lt ht.2⟩) hinit
    exact h q t ⟨ht.1, le_rfl⟩
  intro q t ht
  have hq : ContinuousOn (F q) (Icc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨mem_univ q, hs⟩)
  have hclosure : t ∈ closure (Ico a b) := by
    rw [closure_Ico hab.ne]
    exact ht
  exact ContinuousWithinAt.closure_le hclosure
    ((hq t ht).mono Ico_subset_Icc_self) continuousWithinAt_const (hbefore q)

end Poincare.Parabolic
