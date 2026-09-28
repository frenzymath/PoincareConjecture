import PoincareConjecture.Proofs.M05.Analysis.Parabolic.CompactMaximum

set_option autoImplicit false

open Set

namespace Poincare.Parabolic

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
