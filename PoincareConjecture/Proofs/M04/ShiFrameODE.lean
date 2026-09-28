import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false

open Set
open scoped ContDiff NNReal

namespace PoincareConjecture.M04

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem frame_ode_pairing_eq
    {a b : ℝ} (hab : a < b) (t₀ : Icc a b)
    (A P : ℝ → E →L[ℝ] E)
    (G G' : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hP : ∀ t ∈ Icc a b,
      HasDerivWithinAt P (-((A t).comp (P t))) (Icc a b) t)
    (hG : ∀ t ∈ Icc a b,
      HasDerivWithinAt G (G' t) (Icc a b) t)
    (hcompat : ∀ t ∈ Icc a b, ∀ v w,
      G' t v w = G t (A t v) w + G t v (A t w)) :
    ∀ t ∈ Icc a b, ∀ v w,
      G t (P t v) (P t w) =
        G (t₀ : ℝ) (P (t₀ : ℝ) v) (P (t₀ : ℝ) w) := by
  intro t ht v w
  let S : Set ℝ := Icc a b
  let h : ℝ → ℝ := fun s => G s (P s v) (P s w)
  have hderiv (s : ℝ) (hs : s ∈ S) :
      HasDerivWithinAt h 0 S s := by
    have hpv : HasDerivWithinAt (fun r => P r v)
        ((-((A s).comp (P s))) v) S s := by
      simpa using (hP s hs).clm_apply (hasDerivWithinAt_const s S v)
    have hpw : HasDerivWithinAt (fun r => P r w)
        ((-((A s).comp (P s))) w) S s := by
      simpa using (hP s hs).clm_apply (hasDerivWithinAt_const s S w)
    have hGpv : HasDerivWithinAt (fun r => G r (P r v))
        (G' s (P s v) + G s ((-((A s).comp (P s))) v)) S s := by
      simpa using (hG s hs).clm_apply hpv
    have hall := hGpv.clm_apply hpw
    have hzero :
        G' s (P s v) (P s w) +
            G s ((-((A s).comp (P s))) v) (P s w) +
            G s (P s v) ((-((A s).comp (P s))) w) = 0 := by
      rw [hcompat s hs]
      simp only [ContinuousLinearMap.comp_apply, neg_apply, map_neg]
      ring
    simpa only [h, add_apply, hzero] using hall
  have hdiff : DifferentiableOn ℝ h S := by
    intro s hs
    exact (hderiv s hs).differentiableWithinAt
  have hconst : ∀ s ∈ S, h s = h a := by
    apply constant_of_derivWithin_zero hdiff
    intro s hs
    exact (hderiv s (Ico_subset_Icc_self hs)).derivWithin
      ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt (Ico_subset_Icc_self hs))
  exact (hconst t ht).trans (hconst (t₀ : ℝ) t₀.property).symm

theorem exists_contDiffOn_frame_ode
    {a b : ℝ} (hab : a < b) (t₀ : Icc a b)
    (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc a b))
    (K : ℝ≥0)
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ (K : ℝ))
    (hshort : b - a ≤ 1 / (2 * (K : ℝ) + 1))
    (P₀ : E →L[ℝ] E) :
    ∃ P : ℝ → E →L[ℝ] E,
      ContDiffOn ℝ 1 P (Icc a b) ∧
      P (t₀ : ℝ) = P₀ ∧
      ∀ t ∈ Icc a b,
        HasDerivWithinAt P (-((A t).comp (P t))) (Icc a b) t := by
  let f : ℝ → (E →L[ℝ] E) → E →L[ℝ] E := fun t P => -((A t).comp P)
  let r₀ : ℝ≥0 := ‖P₀‖₊ + 1
  let a₀ : ℝ≥0 := 2 * r₀
  let L₀ : ℝ≥0 := 2 * K * r₀
  have hf : IsPicardLindelof f t₀ (0 : E →L[ℝ] E) a₀ r₀ L₀ K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      refine LipschitzOnWith.of_dist_le_mul (fun P hP Q hQ => ?_)
      change dist (-((A t).comp P)) (-((A t).comp Q)) ≤
        (K : ℝ) * dist P Q
      rw [dist_neg_neg, dist_eq_norm, dist_eq_norm,
        ← ContinuousLinearMap.comp_sub]
      calc
        ‖(A t).comp (P - Q)‖ ≤ ‖A t‖ * ‖P - Q‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * ‖P - Q‖ :=
          mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _)
    · intro P hP
      have hcomp : ContinuousOn (fun t => (A t).comp P) (Icc a b) :=
        hA.clm_comp continuousOn_const
      exact hcomp.neg
    · intro t ht P hP
      have hPnorm : ‖P‖ ≤ (a₀ : ℝ) := by
        simpa [Metric.mem_closedBall, dist_zero_right, a₀] using hP
      calc
        ‖f t P‖ = ‖(A t).comp P‖ := by simp [f]
        _ ≤ ‖A t‖ * ‖P‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * (a₀ : ℝ) := by
          exact mul_le_mul (hK t ht) hPnorm (norm_nonneg _) K.2
        _ = (L₀ : ℝ) := by simp [L₀, a₀]; ring
    · have hspan : max (b - (t₀ : ℝ)) ((t₀ : ℝ) - a) ≤ b - a := by
        apply max_le <;> linarith [t₀.2.1, t₀.2.2]
      have hden : 0 < 2 * (K : ℝ) + 1 := by positivity
      have hfrac : 2 * (K : ℝ) / (2 * (K : ℝ) + 1) ≤ 1 := by
        apply (div_le_iff₀ hden).2
        nlinarith [K.2]
      have hmax : max (b - (t₀ : ℝ)) ((t₀ : ℝ) - a) ≤
          1 / (2 * (K : ℝ) + 1) := hspan.trans hshort
      have hkd : 2 * (K : ℝ) * max (b - (t₀ : ℝ)) ((t₀ : ℝ) - a) ≤ 1 := by
        calc
          2 * (K : ℝ) * max (b - (t₀ : ℝ)) ((t₀ : ℝ) - a) ≤
              2 * (K : ℝ) * (1 / (2 * (K : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hmax (by positivity)
          _ = 2 * (K : ℝ) / (2 * (K : ℝ) + 1) := by ring
          _ ≤ 1 := hfrac
      change (2 * (K : ℝ) * (r₀ : ℝ)) *
        max (b - (t₀ : ℝ)) ((t₀ : ℝ) - a) ≤ 2 * (r₀ : ℝ) - (r₀ : ℝ)
      calc
        (2 * (K : ℝ) * (r₀ : ℝ)) * max (b - (t₀ : ℝ)) ((t₀ : ℝ) - a) =
            (r₀ : ℝ) * (2 * (K : ℝ) * max (b - (t₀ : ℝ)) ((t₀ : ℝ) - a)) := by ring
        _ ≤ (r₀ : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hkd (by positivity)
        _ = 2 * (r₀ : ℝ) - (r₀ : ℝ) := by ring
  have hP₀ : P₀ ∈ Metric.closedBall (0 : E →L[ℝ] E) r₀ := by
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖P₀‖ ≤ ‖P₀‖ + 1
    linarith
  obtain ⟨P, hPinit, hPder⟩ :=
    IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hf hP₀
  have hPder' : ∀ t ∈ Icc a b,
      HasDerivWithinAt P (-((A t).comp (P t))) (Icc a b) t := by
    intro t ht
    simpa [f] using hPder t ht
  have hPcont : ContinuousOn P (Icc a b) := by
    intro t ht
    exact (hPder' t ht).continuousWithinAt
  have hPdiff : DifferentiableOn ℝ P (Icc a b) := by
    intro t ht
    exact (hPder' t ht).differentiableWithinAt
  have hRcont : ContinuousOn (fun t => -((A t).comp (P t))) (Icc a b) := by
    exact (hA.clm_comp hPcont).neg
  have hRderiv : ContinuousOn (derivWithin P (Icc a b)) (Icc a b) := by
    apply hRcont.congr
    intro t ht
    exact (hPder' t ht).derivWithin
      ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt ht)
  refine ⟨P, ?_, hPinit, hPder'⟩
  exact (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).2
    ⟨hPdiff, hRderiv⟩


end PoincareConjecture.M04
