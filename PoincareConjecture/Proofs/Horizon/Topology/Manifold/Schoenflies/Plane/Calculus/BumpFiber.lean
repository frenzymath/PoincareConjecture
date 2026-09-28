import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.ParametricInverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

theorem exists_smooth_fiber_cutoff {r : ℝ} (hr : 0 < r) :
    ∃ β : ℝ → ℝ, ∃ B : ℝ, 0 < B ∧ ContDiff ℝ ∞ β ∧ β 0 = 1 ∧
      (∀ x, 0 ≤ β x ∧ β x ≤ 1) ∧ (∀ x, r ≤ |x| → β x = 0) ∧
      ∀ x, |deriv β x| ≤ B := by
  let β : ℝ → ℝ := fun x => Real.smoothTransition (2 - 2 * (x / r) ^ 2)
  have hβ : ContDiff ℝ ∞ β := Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul ((contDiff_id.div_const r).pow 2)))
  have hzero : ∀ x, r ≤ |x| → β x = 0 := by
    intro x hx
    have hsq : r ^ 2 ≤ x ^ 2 := by
      nlinarith [sq_abs x, mul_nonneg (sub_nonneg.mpr hx)
        (add_nonneg (abs_nonneg x) hr.le)]
    have hq : 1 ≤ (x / r) ^ 2 := by
      rw [div_pow]
      exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa using hsq)
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  have hsupp : HasCompactSupport β := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-r) r))
    intro x hx
    apply hzero x
    by_contra hn
    have ht := abs_lt.mp (lt_of_not_ge hn)
    exact hx ⟨ht.1.le, ht.2.le⟩
  obtain ⟨C, hC⟩ := hsupp.deriv.exists_bound_of_continuous
    (hβ.continuous_deriv (by simp))
  refine ⟨β, max C 0 + 1, by linarith [le_max_right C 0], hβ, ?_, ?_, hzero, ?_⟩
  · norm_num [β, Real.smoothTransition.one_of_one_le]
  · intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro x
    have h := hC x
    rw [Real.norm_eq_abs] at h
    linarith [le_max_left C 0]

theorem exists_smooth_bump_fiber_diffeomorph
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 1)
    (a d : V → ℝ) (ha : ContDiff ℝ ∞ a) (hd : ContDiff ℝ ∞ d)
    {A B r : ℝ} (hderiv : ∀ x, |deriv β x| ≤ B)
    (hsmall : ∀ z, B * |d z| < 1) (hcenter : ∀ z, |a z| ≤ A)
    (hsupport : ∀ x, r ≤ |x| → β x = 0) :
    ∃ D : (V × ℝ) ≃ₘ[ℝ] (V × ℝ),
      (∀ p, D p = (p.1, p.2 + β (p.2 - a p.1) * d p.1)) ∧
      (∀ z, StrictMono (fun x : ℝ => (D (z, x)).2)) ∧
      (∀ z x, x ≤ -A - r ∨ A + r ≤ x → D (z, x) = (z, x)) ∧
      ∀ z, D (z, a z) = (z, a z + d z) := by
  let F : V × ℝ → ℝ := fun p => p.2 + β (p.2 - a p.1) * d p.1
  have hF : ContDiff ℝ ∞ F := contDiff_snd.add
    ((hβ.comp (contDiff_snd.sub (ha.comp contDiff_fst))).mul (hd.comp contDiff_fst))
  have hD : ∀ z x, HasDerivAt (fun y => F (z, y))
      (1 + deriv β (x - a z) * d z) x := by
    intro z x
    convert! (hasDerivAt_id x).add
      ((((hβ.differentiable (by simp)) (x - a z)).hasDerivAt.comp x
        ((hasDerivAt_id x).sub_const (a z))).mul_const (d z)) using 1
    simp
  have hpos : ∀ z x, 0 < deriv (fun y => F (z, y)) x := by
    intro z x
    rw [(hD z x).deriv]
    have hprod : |deriv β (x - a z) * d z| < 1 := calc
      _ = |deriv β (x - a z)| * |d z| := abs_mul _ _
      _ ≤ B * |d z| := mul_le_mul_of_nonneg_right (hderiv _) (abs_nonneg _)
      _ < 1 := hsmall z
    linarith [(abs_lt.mp hprod).1]
  have hfix : ∀ z x, x ≤ -A - r ∨ A + r ≤ x → F (z, x) = x := by
    intro z x hx
    have hsep : r ≤ |x - a z| := by
      rcases hx with hx | hx
      · linarith [(abs_le.mp (hcenter z)).1, neg_le_abs (x - a z)]
      · linarith [(abs_le.mp (hcenter z)).2, le_abs_self (x - a z)]
    simp only [F, hsupport (x - a z) hsep, zero_mul, add_zero]
  have hsurj : ∀ z, Surjective (fun x => F (z, x)) := by
    intro z
    exact surjective_of_eq_self_outside_interval
      (hF.continuous.comp (continuous_const.prodMk continuous_id)) (-A - r) (A + r)
      (hfix z)
  refine ⟨fiberDiffeomorph hF hpos hsurj, ?_, ?_, ?_, ?_⟩
  · intro p
    rfl
  · intro z
    exact strictMono_of_deriv_pos (hpos z)
  · intro z x hx
    change (z, F (z, x)) = (z, x)
    exact Prod.ext rfl (hfix z x hx)
  · intro z
    change (z, a z + β (a z - a z) * d z) = (z, a z + d z)
    simp only [sub_self, hβ0, one_mul]

end Poincare.Manifold.Schoenflies.Plane
