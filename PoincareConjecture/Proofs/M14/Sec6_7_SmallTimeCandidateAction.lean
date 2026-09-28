import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurveEndpoints
import PoincareConjecture.Proofs.M14.Sec6_1_PathCongruence
import PoincareConjecture.Definitions.M14Exponential

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem smallTimeCandidate_action_eq_integral
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    (W : G.Horizontal x) {s d : ℝ} (hs : 0 < s) (hsd : s ≤ d)
    (hD : (W, s) ∈ E.domain)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (E.gamma W) (Icc 0 d))
    (hdom : ∀ r ∈ Icc 0 d, (W, r) ∈ E.domain) :
    M14BackwardLAction G (E.path W s hD hs) =
      ∫ r in 0..s, squareCurveDensity G (E.gamma W) (Icc 0 d) r := by
  have hsub : M14SqrtParameterInterval 0 (s ^ 2) ⊆ Icc 0 d := by
    intro r hr
    simp only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hs.le] at hr
    exact ⟨hr.1, hr.2.trans hsd⟩
  have hclock : ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2),
      G.spacetime.timeFunction (E.gamma W r) = T - r ^ 2 :=
    fun r hr => E.clock W r (hdom r (hsub hr))
  have hx : E.gamma W (Real.sqrt 0) = x := by
    simpa only [Real.sqrt_zero] using E.gamma_at_zero W
  have hy : E.gamma W (Real.sqrt (s ^ 2)) = E.gamma W s := by
    rw [Real.sqrt_sq hs.le]
  let q := backwardPathOfSquareCurveBetween hM12 (le_refl 0) (sq_pos_of_pos hs)
    (E.gamma W) (hγ.mono hsub) hclock hx hy
  have haction : M14BackwardLAction G q = M14BackwardLAction G (E.path W s hD hs) :=
    action_eq_of_curve_eqOn q (E.path W s hD hs) (fun r hr =>
      (E.path_coherent W s hD hs r (Ioo_subset_Icc_self hr)).symm)
  have hint := integral_squareCurveDensity_eq_action_between hM12 (le_refl 0)
    (sq_pos_of_pos hs) (E.gamma W) hγ hsub hclock hx hy
  rw [← haction]
  simpa only [Real.sqrt_zero, Real.sqrt_sq hs.le] using hint.symm

theorem smallTimeCandidate_action_le
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    (W : G.Horizontal x) {s d A : ℝ} (hs : 0 < s) (hsd : s ≤ d)
    (hD : (W, s) ∈ E.domain)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (E.gamma W) (Icc 0 d))
    (hdom : ∀ r ∈ Icc 0 d, (W, r) ∈ E.domain)
    (hA : ∀ r ∈ Icc 0 d, squareCurveDensity G (E.gamma W) (Icc 0 d) r ≤ A) :
    M14BackwardLAction G (E.path W s hD hs) ≤ A * s := by
  rw [smallTimeCandidate_action_eq_integral hM12 E W hs hsd hD hγ hdom]
  have hsub : Icc 0 s ⊆ Icc 0 d := fun _ hr => ⟨hr.1, hr.2.trans hsd⟩
  have hcont := (squareCurveDensity_contDiffOn hM12
    (uniqueDiffOn_Icc (hs.trans_le hsd)) hγ).continuousOn
  have hi : IntervalIntegrable
      (squareCurveDensity G (E.gamma W) (Icc 0 d)) MeasureTheory.volume 0 s :=
    (hcont.mono hsub).intervalIntegrable_of_Icc hs.le
  calc
    (∫ r in 0..s, squareCurveDensity G (E.gamma W) (Icc 0 d) r) ≤
        ∫ _ in 0..s, A :=
      intervalIntegral.integral_mono_on hs.le hi intervalIntegrable_const
        (fun r hr => hA r (hsub hr))
    _ = A * s := by simp [mul_comm]

end PoincareConjecture.M14
