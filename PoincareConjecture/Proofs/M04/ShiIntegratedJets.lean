import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace PoincareConjecture.M04

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

noncomputable def shiIntegratedEnergy (a b : ι → ℝ) (e : ι → ℝ → V → ℝ)
    (z : V) : ℝ := ∑ i, ∫ t in a i..b i, e i t z

noncomputable def shiIntegratedLinearJet (a b : ι → ℝ) (e : ι → ℝ → V → ℝ) :
    V →L[ℝ] ℝ := ∑ i, ∫ t in a i..b i, fderiv ℝ (e i t) 0

noncomputable def shiIntegratedQuadraticJet (a b : ι → ℝ) (e : ι → ℝ → V → ℝ) :
    V →L[ℝ] V →L[ℝ] ℝ := ∑ i, ∫ t in a i..b i, fderiv ℝ (fderiv ℝ (e i t)) 0

theorem shiIntegratedLinearJet_apply
    (a b : ι → ℝ) (e : ι → ℝ → V → ℝ) (hab : ∀ i, a i ≤ b i)
    (hL : ∀ i, ContinuousOn (fun t => fderiv ℝ (e i t) 0) (Icc (a i) (b i)))
    (v : V) :
    shiIntegratedLinearJet a b e v = ∑ i, ∫ t in a i..b i, fderiv ℝ (e i t) 0 v := by
  classical
  simp only [shiIntegratedLinearJet, sum_apply]
  exact Finset.sum_congr rfl (fun i _ => ContinuousLinearMap.intervalIntegral_apply
    (ContinuousOn.intervalIntegrable_of_Icc (hab i) (hL i)) v)

theorem shiIntegratedQuadraticJet_apply
    (a b : ι → ℝ) (e : ι → ℝ → V → ℝ) (hab : ∀ i, a i ≤ b i)
    (hQ : ∀ i, ContinuousOn (fun t => fderiv ℝ (fderiv ℝ (e i t)) 0)
      (Icc (a i) (b i))) (v w : V) :
    shiIntegratedQuadraticJet a b e v w =
      ∑ i, ∫ t in a i..b i, fderiv ℝ (fderiv ℝ (e i t)) 0 v w := by
  classical
  simp only [shiIntegratedQuadraticJet, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.intervalIntegral_apply
    (ContinuousOn.intervalIntegrable_of_Icc (hab i) (hQ i)) v]
  exact ContinuousLinearMap.intervalIntegral_apply
    (ContinuousOn.intervalIntegrable_of_Icc (hab i)
      ((hQ i).clm_apply continuousOn_const)) w

theorem shiIntegratedQuadraticJet_trace
    {κ : Type*} [Fintype κ] (a b : ι → ℝ) (e : ι → ℝ → V → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hQ : ∀ i, ContinuousOn (fun t => fderiv ℝ (fderiv ℝ (e i t)) 0)
      (Icc (a i) (b i))) (v : κ → V) :
    (∑ j, shiIntegratedQuadraticJet a b e (v j) (v j)) =
      ∑ i, ∫ t in a i..b i, ∑ j, fderiv ℝ (fderiv ℝ (e i t)) 0 (v j) (v j) := by
  classical
  simp_rw [shiIntegratedQuadraticJet_apply a b e hab hQ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (intervalIntegral.integral_finsetSum (fun j _ =>
    ContinuousOn.intervalIntegrable_of_Icc (hab i)
      (((hQ i).clm_apply continuousOn_const).clm_apply continuousOn_const))).symm

private theorem norm_sum_intervalIntegral_le
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i) (hsize : ∑ i, (b i - a i) = 1)
    (f : ι → ℝ → Y) (C : ℝ)
    (hf : ∀ i t, t ∈ Icc (a i) (b i) → ‖f i t‖ ≤ C) :
    ‖∑ i, ∫ t in a i..b i, f i t‖ ≤ C := by
  classical
  calc
    ‖∑ i, ∫ t in a i..b i, f i t‖ ≤ ∑ i, ‖∫ t in a i..b i, f i t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, C * (b i - a i) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_of_nonneg (sub_nonneg.mpr (hab i))] using
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := a i) (b := b i) (f := f i) (C := C) (fun t ht =>
          hf i t (Ioc_subset_Icc_self (by simpa only [uIoc_of_le (hab i)] using ht)))
    _ = C := by rw [← Finset.mul_sum, hsize, mul_one]

set_option maxHeartbeats 600000 in

theorem shi_integrated_energy_jets
    (a b : ι → ℝ) (e : ι → ℝ → V → ℝ)
    (hab : ∀ i, a i ≤ b i) (hsize : ∑ i, (b i - a i) = 1)
    (ρ B : ℝ) (hρ : 0 < ρ)
    (he : ∀ i z, ‖z‖ < ρ → ContinuousOn (fun t => e i t z) (Icc (a i) (b i)))
    (hL : ∀ i, ContinuousOn (fun t => fderiv ℝ (e i t) 0) (Icc (a i) (b i)))
    (hQ : ∀ i, ContinuousOn (fun t => fderiv ℝ (fderiv ℝ (e i t)) 0)
      (Icc (a i) (b i)))
    (hbound : ∀ i t, t ∈ Icc (a i) (b i) →
      ‖fderiv ℝ (e i t) 0‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (e i t)) 0‖ ≤ B ∧
      (∀ v w, fderiv ℝ (fderiv ℝ (e i t)) 0 v w =
        fderiv ℝ (fderiv ℝ (e i t)) 0 w v) ∧
      ∀ z, ‖z‖ < ρ →
        |e i t z - e i t 0 - fderiv ℝ (e i t) 0 z -
          fderiv ℝ (fderiv ℝ (e i t)) 0 z z / 2| ≤ B * ‖z‖ ^ 3) :
    ‖shiIntegratedLinearJet a b e‖ ≤ B ∧
      ‖shiIntegratedQuadraticJet a b e‖ ≤ B ∧
      (∀ v w, shiIntegratedQuadraticJet a b e v w =
        shiIntegratedQuadraticJet a b e w v) ∧
      ∀ z, ‖z‖ < ρ →
        |shiIntegratedEnergy a b e z - shiIntegratedEnergy a b e 0 -
          shiIntegratedLinearJet a b e z - shiIntegratedQuadraticJet a b e z z / 2| ≤
            B * ‖z‖ ^ 3 := by
  classical
  refine ⟨norm_sum_intervalIntegral_le a b hab hsize _ B
    (fun i t ht => (hbound i t ht).1),
    norm_sum_intervalIntegral_le a b hab hsize _ B
      (fun i t ht => (hbound i t ht).2.1), ?_, ?_⟩
  · intro v w
    rw [shiIntegratedQuadraticJet_apply a b e hab hQ,
      shiIntegratedQuadraticJet_apply a b e hab hQ]
    apply Finset.sum_congr rfl
    intro i _
    apply intervalIntegral.integral_congr
    intro t ht
    exact (hbound i t (by simpa only [uIcc_of_le (hab i)] using ht)).2.2.1 v w
  · intro z hz
    let R : ι → ℝ → ℝ := fun i t => e i t z - e i t 0 -
      fderiv ℝ (e i t) 0 z - fderiv ℝ (fderiv ℝ (e i t)) 0 z z / 2
    have hR : ‖∑ i, ∫ t in a i..b i, R i t‖ ≤ B * ‖z‖ ^ 3 :=
      norm_sum_intervalIntegral_le a b hab hsize R (B * ‖z‖ ^ 3)
        (fun i t ht => by simpa only [R, Real.norm_eq_abs] using
          (hbound i t ht).2.2.2 z hz)
    have hint (i : ι) : (∫ t in a i..b i, R i t) =
        (∫ t in a i..b i, e i t z) - (∫ t in a i..b i, e i t 0) -
          (∫ t in a i..b i, fderiv ℝ (e i t) 0 z) -
          (∫ t in a i..b i, fderiv ℝ (fderiv ℝ (e i t)) 0 z z) / 2 := by
      have hez : IntervalIntegrable (fun t => e i t z) volume (a i) (b i) :=
        ContinuousOn.intervalIntegrable_of_Icc (hab i) (he i z hz)
      have he0 : IntervalIntegrable (fun t => e i t 0) volume (a i) (b i) :=
        ContinuousOn.intervalIntegrable_of_Icc (hab i)
        (he i 0 (by simpa using hρ))
      have hLv : IntervalIntegrable (fun t => fderiv ℝ (e i t) 0 z)
          volume (a i) (b i) := ContinuousOn.intervalIntegrable_of_Icc (hab i)
        ((hL i).clm_apply continuousOn_const)
      have hQvv : IntervalIntegrable (fun t => fderiv ℝ (fderiv ℝ (e i t)) 0 z z)
          volume (a i) (b i) := ContinuousOn.intervalIntegrable_of_Icc (hab i)
        (((hQ i).clm_apply continuousOn_const).clm_apply continuousOn_const)
      dsimp only [R]
      rw [intervalIntegral.integral_sub ((hez.sub he0).sub hLv) (hQvv.div_const 2),
        intervalIntegral.integral_sub (hez.sub he0) hLv,
        intervalIntegral.integral_sub hez he0, intervalIntegral.integral_div]
    rw [shiIntegratedLinearJet_apply a b e hab hL,
      shiIntegratedQuadraticJet_apply a b e hab hQ]
    simp only [hint, Finset.sum_sub_distrib, ← Finset.sum_div, Real.norm_eq_abs] at hR
    exact hR

end PoincareConjecture.M04
