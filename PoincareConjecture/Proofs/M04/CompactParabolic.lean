import PoincareConjecture.Proofs.M04.ScalarEstimates
import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M04

theorem compact_min_velocity_nonnegative
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {T K : ℝ} (hT : 0 < T) (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set M)))
    (hderiv : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc 0 T) t)
    (hmin : ∀ t ∈ Ioc 0 T, ∀ x : M,
      (∀ y : M, f t x ≤ f t y) → f t x ≤ 0 → -K * f t x ≤ v t x)
    (hinit : ∀ x : M, 0 ≤ f 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x : M, 0 ≤ f t x := by
  intro t ht x
  by_contra hbad
  have hbad' : f t x < 0 := lt_of_not_ge hbad
  let q := Real.exp (K * t) * f t x
  have hq : q < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) hbad'
  let ε := -q / (T + 1)
  have heps : 0 < ε := div_pos (neg_pos.mpr hq) (by linarith)
  have heps_eq : ε * (T + 1) = -q :=
    div_mul_cancel₀ (-q) (ne_of_gt (by linarith : 0 < T + 1))
  let w : ℝ → M → ℝ := fun s y ↦ Real.exp (K * s) * f s y + ε * s
  have hwbad : w t x < 0 := by
    have hlt := mul_lt_mul_of_pos_left (show t < T + 1 by linarith [ht.2]) heps
    change q + ε * t < 0
    linarith
  let S : Set (ℝ × M) := Icc 0 t ×ˢ univ
  have hsub : S ⊆ Icc 0 T ×ˢ (univ : Set M) :=
    fun p hp ↦ ⟨⟨hp.1.1, hp.1.2.trans ht.2⟩, hp.2⟩
  have hwc : ContinuousOn (Function.uncurry w) S :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).continuousOn.mul
      (hf.mono hsub)).add (continuous_const.mul continuous_fst).continuousOn
  obtain ⟨⟨s, y⟩, hsy, hminw⟩ := (isCompact_Icc.prod isCompact_univ).exists_isMinOn
    (show S.Nonempty from ⟨(0, x), ⟨⟨le_rfl, ht.1⟩, mem_univ x⟩⟩) hwc
  change (s ∈ Icc 0 t) ∧ y ∈ (univ : Set M) at hsy
  have hwy : w s y < 0 :=
    (hminw (show (t, x) ∈ S from ⟨⟨ht.1, le_rfl⟩, mem_univ x⟩)).trans_lt hwbad
  have hspos : 0 < s := by
    rcases lt_or_eq_of_le hsy.1.1 with hs | hs
    · exact hs
    · have : w s y = f 0 y := by simp [w, ← hs]
      rw [this] at hwy
      exact False.elim ((not_lt_of_ge (hinit y)) hwy)
  have hsJ : s ∈ Icc 0 T := ⟨hspos.le, hsy.1.2.trans ht.2⟩
  have hspace : ∀ z : M, f s y ≤ f s z := by
    intro z
    have h := hminw (show (s, z) ∈ S from ⟨hsy.1, mem_univ z⟩)
    change Real.exp (K * s) * f s y + ε * s ≤
      Real.exp (K * s) * f s z + ε * s at h
    exact le_of_mul_le_mul_left (add_le_add_iff_right (ε * s) |>.mp h) (Real.exp_pos _)
  have hfneg : f s y < 0 := by
    by_contra h
    have hprod := mul_nonneg (Real.exp_pos (K * s)).le (le_of_not_gt h)
    have htime := mul_nonneg heps.le hspos.le
    change Real.exp (K * s) * f s y + ε * s < 0 at hwy
    linarith
  have hvelocity : 0 ≤ v s y + K * f s y := by
    have := hmin s ⟨hspos, hsJ.2⟩ y hspace hfneg.le
    linarith
  have hpos : 0 < Real.exp (K * s) * (v s y + K * f s y) + ε :=
    add_pos_of_nonneg_of_pos (mul_nonneg (Real.exp_pos _).le hvelocity) heps
  have htime : IsMinOn (fun r ↦ w r y) (Icc 0 s) s := by
    intro r hr
    exact hminw (show (r, y) ∈ S from ⟨⟨hr.1, hr.2.trans hsy.1.2⟩, mem_univ y⟩)
  have hdexp : HasDerivAt (fun r : ℝ ↦ Real.exp (K * r))
      (Real.exp (K * s) * K) s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul K).exp
  have hdw : HasDerivWithinAt (fun r ↦ w r y)
      (Real.exp (K * s) * (v s y + K * f s y) + ε) (Icc 0 s) s := by
    have hdf : HasDerivWithinAt (fun r ↦ f r y) (v s y) (Icc 0 s) s :=
      (hderiv s hsJ y).mono
        (show Icc 0 s ⊆ Icc 0 T from fun r hr ↦ ⟨hr.1, hr.2.trans hsJ.2⟩)
    have hdl : HasDerivWithinAt (fun r : ℝ ↦ ε * r) ε (Icc 0 s) s := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id s).const_mul ε).hasDerivWithinAt)
    change HasDerivWithinAt (fun r ↦ Real.exp (K * r) * f r y + ε * r) _ _ _
    convert! (hdexp.hasDerivWithinAt.mul hdf).add hdl using 1
    ring
  have hcone : 0 - s ∈ posTangentConeAt (Icc 0 s) s :=
    sub_mem_posTangentConeAt_of_segment_subset
      (by rw [segment_symm, segment_eq_Icc hspos.le])
  have hsign : 0 ≤ (0 - s) * (Real.exp (K * s) * (v s y + K * f s y) + ε) := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      using htime.localize.hasFDerivWithinAt_nonneg hdw hcone
  exact (not_le_of_gt (mul_neg_of_neg_of_pos (sub_neg.mpr hspos) hpos)) hsign

theorem ricciFlow_supersolution_nonnegative
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] {T K : ℝ} (hT : 0 < T) (F : RicciFlow n M (Icc 0 T))
    (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set M)))
    (hderiv : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc 0 T) t)
    (hinit : ∀ x : M, 0 ≤ f 0 x)
    (hsmooth : ∀ t ∈ Icc 0 T, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f t))
    (hevol : ∀ t ∈ Ioc 0 T, ∀ x : M,
      (F.connection t).laplacian (f t) x - K * f t x ≤ v t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M, 0 ≤ f t x := by
  apply compact_min_velocity_nonnegative (K := K) hT f v hf hderiv _ hinit
  intro t ht x hmin _hneg
  have hlocal : IsLocalMin (f t) x := Filter.Eventually.of_forall hmin
  have hlap := (F.connection t).laplacian_nonneg_of_isLocalMin
    ((hsmooth t ⟨ht.1.le, ht.2⟩).contMDiffAt) hlocal
  have := hevol t ht x
  linarith

end PoincareConjecture.M04
