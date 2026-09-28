import PoincareConjecture.Proofs.M34.Standard.LeastSectional
import PoincareConjecture.Proofs.M34.Standard.SectionalHeatComparison
import PoincareConjecture.Proofs.M04.LocalScalarBarrier










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open M04




theorem sectional_compact_moving_barrier
    {J : Set ℝ} {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 (EuclideanSpace ℝ (Fin 3)) J) (hJ : Icc a b ⊆ J)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    {q : EuclideanSpace ℝ (Fin 3) → ℝ} (hq : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ q)
    {speed : ℝ}
    (hcritical : ∀ t ∈ Icc a b, ∀ x ∈ K,
      q x + speed * (t - a) = 0 → mfderiv (𝓡 3) 𝓘(ℝ, ℝ) q x ≠ 0)
    (hnonneg : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hboundary : ∀ t ∈ Icc a b, ∀ x ∈ K \ interior K,
      q x + speed * (t - a) ≤ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ epsilon : ℝ, 0 ≤ epsilon →
      (∀ x ∈ K, epsilon * expNegInvGlue (q x) ≤ modelLeastSectional (F.connection a) x) →
      ∀ t ∈ Icc a b, ∀ x ∈ K,
        epsilon * Real.exp (-A * (t - a)) * expNegInvGlue (q x + speed * (t - a)) ≤
          modelLeastSectional (F.connection t) x := by
  obtain ⟨A, hA, hbar⟩ := exists_moving_scalar_barrier_decay_Icc F hJ isOpen_univ
    hq.contMDiffOn hK (subset_univ K) hcritical
  refine ⟨A, hA, fun epsilon hepsilon hinit => ?_⟩
  let B := fun t x => epsilon * Real.exp (-A * (t - a)) *
    expNegInvGlue (q x + speed * (t - a))
  let V := fun t x => epsilon * Real.exp (-A * (t - a)) *
    (-A * expNegInvGlue (q x + speed * (t - a)) +
      speed * deriv expNegInvGlue (q x + speed * (t - a)))
  have hqC : ContinuousOn (fun z : ℝ × EuclideanSpace ℝ (Fin 3) => q z.2)
      (Icc a b ×ˢ K) := (hq.continuous.comp continuous_snd).continuousOn
  have hBC : ContinuousOn (Function.uncurry B) (Icc a b ×ˢ K) :=
    (continuousOn_const.mul
      ((continuous_const.mul (continuous_fst.sub continuous_const)).rexp.continuousOn)).mul
      ((expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).continuous.comp_continuousOn
        (hqC.add (continuous_const.mul (continuous_fst.sub continuous_const)).continuousOn))
  have hBs (t : ℝ) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (B t) :=
    contMDiff_const.mul
      (expNegInvGlue.contDiff.contMDiff.comp (hq.add contMDiff_const))
  have hBd (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
      HasDerivAt (fun s => B s x) (V t x) t := by
    have h := (hasDerivAt_moving_scalar_barrier q A speed epsilon (t - a) x).comp t
      ((hasDerivAt_id t).sub_const a)
    simpa only [Function.comp_def, id_eq, mul_one] using h
  have hbnd (t : ℝ) (ht : t ∈ Icc a b) (x : EuclideanSpace ℝ (Fin 3))
      (hx : x ∈ K \ interior K) : B t x ≤ 0 := by
    simp only [B, expNegInvGlue.zero_of_nonpos (hboundary t ht x hx), mul_zero, le_refl]
  have hi (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ K)
      (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
      (hp : p ∈ modelOrthonormalPairs 3) :
      B a x ≤ (F.connection a).curvatureTensor x p.1 p.2 p.1 p.2 /
        metricGram (F.metric a) x p.1 p.2 := by
    simpa only [B, sub_self, mul_zero, Real.exp_zero, mul_one, add_zero] using
      (hinit x hx).trans (modelLeastSectional_le (F.connection a) x p hp)
  have hcomp := sectional_ge_heat_subsolution_on_compact hab F hJ hK B V hBC
    (fun t _ => hBs t) (fun t _ x _ => (hBd t x).hasDerivWithinAt)
    (fun t ht x hx => hbar epsilon hepsilon t ⟨ht.1.le, ht.2⟩ x (interior_subset hx))
    hbnd hnonneg hi
  exact fun t ht x hx => le_modelLeastSectional (F.connection t) x (hcomp t ht x hx)

end PoincareConjecture.M34
