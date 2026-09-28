import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.RampLabelOscillation
import Mathlib.Topology.Order.MonotoneContinuity












set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}






theorem positive_ramp_lift_orderIso
    (P : M62.CircleProductData F circumference) (gamma : ℝ → P.charts.Point)
    (L : M63PositiveDegreeLift P gamma) :
    ∃ H : ℝ ≃o ℝ, ∀ x, H x = L.lift x := by
  have hstrict : StrictMono L.lift := strictMono_of_deriv_pos L.derivative_positive
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let D := (L.degree : ℝ) * circumference
  have hD : 0 < D := by
    have hh := hstrict hP
    have hp := L.period_shift 0
    simp only [zero_add] at hp
    dsimp only [D]
    linarith
  have hperiod : Function.Periodic (fun x => L.lift x - D / curvePeriod * x) curvePeriod := by
    intro x
    dsimp only
    rw [L.period_shift]
    dsimp only [D]
    field_simp
    ring
  have hint (k : ℤ) : L.lift ((k : ℝ) * curvePeriod) = L.lift 0 + (k : ℝ) * D := by
    have hh := hperiod.int_mul_eq k
    have hcancel : D / curvePeriod * ((k : ℝ) * curvePeriod) = (k : ℝ) * D := by
      field_simp
    simp only [mul_zero, sub_zero, hcancel] at hh
    linarith
  have hsurj : Function.Surjective L.lift := by
    intro y
    let k : ℤ := ⌊(y - L.lift 0) / D⌋
    have hlo : (k : ℝ) * D ≤ y - L.lift 0 :=
      (le_div_iff₀ hD).mp (Int.floor_le _)
    have hhi : y - L.lift 0 < ((k : ℝ) + 1) * D :=
      (div_lt_iff₀ hD).mp (Int.lt_floor_add_one _)
    apply intermediate_value_univ ((k : ℝ) * curvePeriod)
      (((k + 1 : ℤ) : ℝ) * curvePeriod) L.regular.continuous
    rw [hint k, hint (k + 1)]
    simp only [Int.cast_add, Int.cast_one]
    constructor <;> linarith
  exact ⟨hstrict.orderIsoOfSurjective L.lift hsurj, fun _ => rfl⟩






theorem positive_ramp_phase_recovers_label
    (P : M62.CircleProductData F circumference) (gamma : ℝ → P.charts.Point)
    (L : M63PositiveDegreeLift P gamma)
    (c : ℝ → ℝ) (hc : Continuous c) (hmono : Monotone c)
    (hp : ∀ x, c (x + curvePeriod) = c x + (L.degree : ℝ) * circumference) :
    ∃ sigma : ℝ → ℝ, Continuous sigma ∧ Monotone sigma ∧
      (∀ x, sigma (x + curvePeriod) = sigma x + curvePeriod) ∧
      (∀ x, L.lift (sigma x) = c x) ∧
      ∀ (f : ℕ → ℝ → ℝ),
        (∀ x, Tendsto (fun j => L.lift (f j x)) atTop (𝓝 (c x))) →
        ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (sigma x)) := by
  obtain ⟨H, hH⟩ := positive_ramp_lift_orderIso P gamma L
  let sigma := fun x => H.symm (c x)
  have htrace (x : ℝ) : L.lift (sigma x) = c x := by
    rw [← hH]
    exact H.apply_symm_apply (c x)
  have hperiod (x : ℝ) : sigma (x + curvePeriod) = sigma x + curvePeriod := by
    apply (strictMono_of_deriv_pos L.derivative_positive).injective
    rw [htrace, L.period_shift, htrace, hp]
  refine ⟨sigma, H.symm.continuous.comp hc, H.symm.monotone.comp hmono, hperiod, htrace, ?_⟩
  intro f hf x
  have ht := (H.symm.continuous.tendsto (c x)).comp (hf x)
  have heq (j : ℕ) : H.symm (L.lift (f j x)) = f j x := by
    rw [← hH]
    exact H.symm_apply_apply (f j x)
  simpa only [Function.comp_def, heq, sigma] using ht

end PoincareConjecture.M64
