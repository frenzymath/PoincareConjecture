import PoincareConjecture.Proofs.M25.Topology3D.Plane.BumpFiber
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RadialFiberDiffeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_smooth_interval_cutoff (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ → ℝ, ContDiff ℝ ∞ τ ∧
      (∀ z, 0 ≤ τ z ∧ τ z ≤ 1) ∧
      (∀ z ∈ Icc a b, τ z = 1) ∧
      ∀ z, z ≤ a - ε ∨ b + ε ≤ z → τ z = 0 := by
  let τ : ℝ → ℝ := fun z => Real.smoothTransition ((z - a + ε) / ε) *
    Real.smoothTransition ((b + ε - z) / ε)
  have hτ : ContDiff ℝ ∞ τ :=
    (Real.smoothTransition.contDiff.comp
      (((contDiff_id.sub contDiff_const).add contDiff_const).div_const ε)).mul
        (Real.smoothTransition.contDiff.comp
          ((contDiff_const.sub contDiff_id).div_const ε))
  refine ⟨τ, hτ, ?_, ?_, ?_⟩
  · intro z
    dsimp only [τ]
    constructor
    · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    · nlinarith [Real.smoothTransition.nonneg ((z - a + ε) / ε),
        Real.smoothTransition.nonneg ((b + ε - z) / ε),
        Real.smoothTransition.le_one ((z - a + ε) / ε),
        Real.smoothTransition.le_one ((b + ε - z) / ε)]
  · intro z hz
    have hl : 1 ≤ (z - a + ε) / ε := (le_div_iff₀ hε).2 (by linarith [hz.1])
    have hr : 1 ≤ (b + ε - z) / ε := (le_div_iff₀ hε).2 (by linarith [hz.2])
    simp only [τ, Real.smoothTransition.one_of_one_le hl,
      Real.smoothTransition.one_of_one_le hr, mul_one]
  · intro z hz
    rcases hz with hz | hz
    · have h : (z - a + ε) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
      simp only [τ, Real.smoothTransition.zero_of_nonpos h, zero_mul]
    · have h : (b + ε - z) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
      simp only [τ, Real.smoothTransition.zero_of_nonpos h, mul_zero]



theorem isCompact_time_closedAnnulus
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E] (l u w : ℝ) :
    IsCompact (Icc l u ×ˢ {x : E | |‖x‖ - 1| ≤ w}) := by
  have hs : IsClosed {x : E | |‖x‖ - 1| ≤ w} :=
    isClosed_le (continuous_norm.sub continuous_const).abs continuous_const
  have hsub : {x : E | |‖x‖ - 1| ≤ w} ⊆ closedBall 0 (1 + w) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    change |‖x‖ - 1| ≤ w at hx
    linarith [le_abs_self (‖x‖ - 1)]
  exact isCompact_Icc.prod ((isCompact_closedBall 0 (1 + w)).of_isClosed_subset hs hsub)



theorem exists_supported_radial_bump_slide
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 1)
    (a d : ℝ × E → ℝ) (ha : ContDiff ℝ ∞ a) (hd : ContDiff ℝ ∞ d)
    {A B r l u : ℝ} (hderiv : ∀ x, |deriv β x| ≤ B)
    (hsmall : ∀ v, B * |d v| < 1) (hcenter : ∀ v, |a v| ≤ A)
    (hsupport : ∀ x, r ≤ |x| → β x = 0) (hr : 0 < r) (hwidth : A + r < 1)
    (htime : ∀ v : ℝ × E, v.1 ∉ Icc l u → d v = 0) :
    ∃ R : (ℝ × E) ≃ₘ[ℝ] (ℝ × E),
      (∀ p, R p = radialFiberMap
        (fun v : (ℝ × E) × ℝ => v.2 + β (v.2 - a v.1) * d v.1) p) ∧
      (∀ p, (R p).1 = p.1 ∧ (R.symm p).1 = p.1) ∧
      (∀ p, p.1 ∉ Icc l u ∨ A + r ≤ |‖p.2‖ - 1| → R p = p) ∧
      (∀ z : ℝ, ∀ q : E, ‖q‖ = 1 →
        R (z, (1 + a (z, q)) • q) = (z, (1 + a (z, q) + d (z, q)) • q)) ∧
      HasCompactSupport (fun p => R p - p) ∧
      HasCompactSupport (fun p => R.symm p - p) := by
  obtain ⟨D, hD, hmono, htail, hcenterD⟩ :=
    exists_smooth_bump_fiber_diffeomorph β hβ hβ0 a d ha hd hderiv hsmall hcenter hsupport
  have hparam (p : (ℝ × E) × ℝ) : (D p).1 = p.1 := by rw [hD]
  have hfix (p : (ℝ × E) × ℝ) (hp : A + r ≤ |p.2|) : D p = p := by
    apply htail
    by_cases hs : 0 ≤ p.2
    · exact Or.inr (by simpa only [abs_of_nonneg hs] using hp)
    · left
      rw [abs_of_neg (lt_of_not_ge hs)] at hp
      linarith
  obtain ⟨R, hR, _, hRfix, hRtime⟩ :=
    exists_radialFiberDiffeomorph D hparam hwidth hmono hfix
  let F : (ℝ × E) × ℝ → ℝ := fun v => v.2 + β (v.2 - a v.1) * d v.1
  have hF : (fun v => (D v).2) = F := funext (fun v => congrArg Prod.snd (hD v))
  have hRform (p : ℝ × E) : R p = radialFiberMap F p := by rw [hR, hF]
  have hfixed (p : ℝ × E)
      (hp : p.1 ∉ Icc l u ∨ A + r ≤ |‖p.2‖ - 1|) : R p = p := by
    rcases hp with hp | hp
    · rw [hRform]
      apply radialFiberMap_eq_self
      simp only [F, htime (p.1, NormedSpace.normalize p.2) hp, mul_zero, add_zero]
    · exact hRfix p hp
  have hgraph (z : ℝ) (q : E) (hq : ‖q‖ = 1) :
      R (z, (1 + a (z, q)) • q) = (z, (1 + a (z, q) + d (z, q)) • q) := by
    have hinput : -1 < a (z, q) := by linarith [(abs_le.mp (hcenter (z, q))).1]
    rw [hRform, radialFiberMap_apply_radial F z q hq hinput]
    simp only [F, sub_self, hβ0, one_mul, add_assoc]
  let K : Set (ℝ × E) := Icc l u ×ˢ {x : E | |‖x‖ - 1| ≤ A + r}
  have hK : IsCompact K := isCompact_time_closedAnnulus l u (A + r)
  have hKfix (p : ℝ × E) (hp : p ∉ K) : R p = p := by
    apply hfixed
    by_cases hz : p.1 ∈ Icc l u
    · right
      have hn : ¬ |‖p.2‖ - 1| ≤ A + r := fun h => hp ⟨hz, h⟩
      exact (lt_of_not_ge hn).le
    · exact Or.inl hz
  refine ⟨R, hRform, hRtime, hfixed, hgraph, ?_, ?_⟩
  · exact HasCompactSupport.intro hK (fun p hp => sub_eq_zero.mpr (hKfix p hp))
  · apply HasCompactSupport.intro hK
    intro p hp
    apply sub_eq_zero.mpr
    have h := congrArg R.symm (hKfix p hp)
    simpa only [R.symm_apply_apply] using h.symm

end PoincareConjecture.M25.Topology3D
