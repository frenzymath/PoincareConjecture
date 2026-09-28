import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UnitSpeedInitialPeriod
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FixedArcLength










set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture

open M62

variable {n : Nat} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : Real}



theorem m63ArcLength_exists_centered_enlargement
    (F : RicciFlow n M (Icc a b)) (c : Real → Real → M)
    (hc : M62ShrinkingCurve F c) {s r alpha beta : Real}
    (hs : s ∈ Icc a b) (hr : 0 < r) (hrL : r ≤ m62Length F c s)
    (hab : alpha ≤ beta) (_habPeriod : beta ≤ alpha + curvePeriod)
    (hsmall : m63ArcLength F c s alpha beta ≤ r / 2) :
    ∃ lo x0 hi : Real,
      lo ≤ alpha ∧ alpha ≤ x0 ∧ x0 ≤ beta ∧ beta ≤ hi ∧
      hi ≤ lo + curvePeriod ∧
      m63ArcLength F c s lo x0 = r / 2 ∧
      m63ArcLength F c s x0 hi = r / 2 ∧
      m63ArcLength F c s lo hi = r ∧
      m63ArcLength F c s alpha x0 = m63ArcLength F c s alpha beta / 2 ∧
      m63ArcLength F c s x0 beta = m63ArcLength F c s alpha beta / 2 := by
  obtain ⟨_, sigma, hformula, _, _, _, hpos, _, hshift, _⟩ :=
    M63.exists_c2_unit_speed_parameter F (fun x => c x s) s
      (hc.periodic s hs) (hc.spatial_regular s hs) (hc.immersed s hs)
  have hmono : StrictMono (sigma : Real → Real) := strictMono_of_deriv_pos hpos
  have hV : Continuous (curveSpeed F c s) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, hs⟩)
  have hprimitive (u v : Real) :
      m63ArcLength F c s u v = sigma v - sigma u := by
    rw [hformula v, hformula u]
    exact (intervalIntegral.integral_interval_sub_left
      (hV.intervalIntegrable 0 v) (hV.intervalIntegrable 0 u)).symm
  have hshift' (x : Real) :
      sigma (x + curvePeriod) = sigma x + m62Length F c s := hshift x
  let middle : Real := (sigma alpha + sigma beta) / 2
  let lo : Real := sigma.symm (middle - r / 2)
  let x0 : Real := sigma.symm middle
  let hi : Real := sigma.symm (middle + r / 2)
  have hlo : sigma lo = middle - r / 2 := sigma.apply_symm_apply _
  have hx0 : sigma x0 = middle := sigma.apply_symm_apply _
  have hhi : sigma hi = middle + r / 2 := sigma.apply_symm_apply _
  have hab' := hmono.monotone hab
  have hsmall' : sigma beta - sigma alpha ≤ r / 2 := by
    rwa [hprimitive] at hsmall
  refine ⟨lo, x0, hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hmono.le_iff_le.mp
    rw [hlo]
    dsimp only [middle]
    linarith
  · apply hmono.le_iff_le.mp
    rw [hx0]
    dsimp only [middle]
    linarith
  · apply hmono.le_iff_le.mp
    rw [hx0]
    dsimp only [middle]
    linarith
  · apply hmono.le_iff_le.mp
    rw [hhi]
    dsimp only [middle]
    linarith
  · apply hmono.le_iff_le.mp
    rw [hhi, hshift', hlo]
    linarith
  · rw [hprimitive, hx0, hlo]
    ring
  · rw [hprimitive, hhi, hx0]
    ring
  · rw [hprimitive, hhi, hlo]
    ring
  · rw [hprimitive, hprimitive, hx0]
    dsimp only [middle]
    ring
  · rw [hprimitive, hprimitive, hx0]
    dsimp only [middle]
    ring



theorem m63ArcCutoff_eq_one_of_half_lengths
    (F : RicciFlow n M (Icc a b)) (c : Real → Real → M)
    (hc : M62ShrinkingCurve F c) {K0 K1 K2 : Real}
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s t r alpha beta x0 : Real}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hr : 0 < r) (hleft : alpha ≤ x0) (hright : x0 ≤ beta)
    (hleftLength : m63ArcLength F c s alpha x0 ≤ r / 4)
    (hrightLength : m63ArcLength F c s x0 beta ≤ r / 4)
    (hexp : Real.exp (K2 * (t - s)) ≤ 3 / 2)
    (psi : Real → Real)
    (hplateau : ∀ z, |z| ≤ 3 / 8 → psi z = 1) :
    ∀ x ∈ Icc alpha beta, psi (m63ArcLength F c t x0 x / r) = 1 := by
  have hleftBound : m63ArcLength F c t alpha x0 ≤ 3 * r / 8 := by
    calc
      _ ≤ m63ArcLength F c s alpha x0 * Real.exp (K2 * (t - s)) :=
        m63ArcLength_le_mul_exp F c hc hBounds hleft hs ht hst
      _ ≤ (r / 4) * Real.exp (K2 * (t - s)) :=
        mul_le_mul_of_nonneg_right hleftLength (Real.exp_pos _).le
      _ ≤ (r / 4) * (3 / 2) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 3 * r / 8 := by ring
  have hrightBound : m63ArcLength F c t x0 beta ≤ 3 * r / 8 := by
    calc
      _ ≤ m63ArcLength F c s x0 beta * Real.exp (K2 * (t - s)) :=
        m63ArcLength_le_mul_exp F c hc hBounds hright hs ht hst
      _ ≤ (r / 4) * Real.exp (K2 * (t - s)) :=
        mul_le_mul_of_nonneg_right hrightLength (Real.exp_pos _).le
      _ ≤ (r / 4) * (3 / 2) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 3 * r / 8 := by ring
  have hV : Continuous (curveSpeed F c t) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht⟩)
  intro x hx
  have hbound : |m63ArcLength F c t x0 x| ≤ 3 * r / 8 := by
    obtain hxx0 | hx0x := le_total x x0
    · have hnonneg : 0 ≤ m63ArcLength F c t x x0 :=
        intervalIntegral.integral_nonneg_of_forall hxx0 (speed_nonneg F c t)
      have hcompare : m63ArcLength F c t x x0 ≤
          m63ArcLength F c t alpha x0 :=
        intervalIntegral.integral_mono_interval hx.1 hxx0 le_rfl
          (Filter.Eventually.of_forall (speed_nonneg F c t))
          (hV.intervalIntegrable _ _)
      have hreverse : m63ArcLength F c t x0 x = -m63ArcLength F c t x x0 :=
        intervalIntegral.integral_symm x x0
      rw [hreverse, abs_neg, abs_of_nonneg hnonneg]
      exact hcompare.trans hleftBound
    · have hnonneg : 0 ≤ m63ArcLength F c t x0 x :=
        intervalIntegral.integral_nonneg_of_forall hx0x (speed_nonneg F c t)
      have hcompare : m63ArcLength F c t x0 x ≤
          m63ArcLength F c t x0 beta :=
        intervalIntegral.integral_mono_interval le_rfl hx0x hx.2
          (Filter.Eventually.of_forall (speed_nonneg F c t))
          (hV.intervalIntegrable _ _)
      rw [abs_of_nonneg hnonneg]
      exact hcompare.trans hrightBound
  apply hplateau
  rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
  linarith

end PoincareConjecture
