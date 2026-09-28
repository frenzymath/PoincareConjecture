import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.DivergenceMollification
import PoincareConjecture.Proofs.Horizon.Analysis.Convolution.FluxCommutator
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open Set Filter MeasureTheory
open Poincare.Analysis.Convolution
open scoped Topology ContDiff Convolution NNReal

noncomputable section

set_option maxHeartbeats 800000

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

def mollifiedValue (u ρ : Spacetime n → ℝ) (r : ℝ) (z : Spacetime n) : ℝ :=
  lebesgueConvolution (rescaledKernel ρ r) u z

def mollifiedScalarForcing (C : Coefficients n) (u ρ : Spacetime n → ℝ)
    (r : ℝ) (z : Spacetime n) : ℝ :=
  lebesgueConvolution (rescaledKernel ρ r)
    (fun y => ((∑ i, spatialDeriv i
      (fun w => C.drift i w + ∑ j, spatialDeriv j (C.principal j i) w) y) -
      C.zeroth y) * u y) z

def mollifiedFluxForcing (C : Coefficients n) (u ρ : Spacetime n → ℝ)
    (r : ℝ) (i : Fin n) (z : Spacetime n) : ℝ :=
  -(∑ j, (C.principal i j z * spatialDeriv j
      (mollifiedValue u ρ r) z -
    lebesgueConvolution (fun y => spatialDeriv j (rescaledKernel ρ r) y)
      (fun w => C.principal i j w * u w) z +
    lebesgueConvolution (rescaledKernel ρ r)
      (fun w => spatialDeriv j (C.principal i j) w * u w) z)) -
    lebesgueConvolution (rescaledKernel ρ r)
      (fun w => (C.drift i w + ∑ j, spatialDeriv j (C.principal j i) w) * u w) z

private theorem abs_rescaledKernel_mass
    {ρ : Spacetime n → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hρc : HasCompactSupport ρ) {r : ℝ} (hr : 0 < r) :
    (∫ y, |rescaledKernel ρ r y|) = ∫ y, |ρ y| := by
  have habs : (fun y => |rescaledKernel ρ r y|) =
      rescaledKernel (fun y => |ρ y|) r := by
    funext y
    simp only [rescaledKernel, abs_mul, abs_inv, abs_pow, abs_of_pos hr]
  rw [habs, integral_rescaledKernel volume _ hr]

private theorem abs_rescaled_convolution_le
    {ρ u : Spacetime n → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hρc : HasCompactSupport ρ) (hu : Continuous u) {M : ℝ}
    (hM : ∀ y, |u y| ≤ M) {r : ℝ} (hr : 0 < r) (z : Spacetime n) :
    |lebesgueConvolution (rescaledKernel ρ r) u z| ≤
      M * ∫ y, |ρ y| := by
  have hκ : Continuous (rescaledKernel ρ r) :=
    (contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))).continuous
  have hκc : HasCompactSupport (rescaledKernel ρ r) :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  rw [lebesgueConvolution_eq_convolution]
  simpa only [abs_rescaledKernel_mass hρ hρc hr] using
    (abs_convolution_le_of_bound volume hκ hκc hu hM z)

theorem exists_uniform_mollified_forcing_bounds
    {C : Coefficients n} {u ρ : Spacetime n → ℝ}
    (hprincipal : ∀ i j, ContDiff ℝ ∞ (C.principal i j))
    (hprincipalc : ∀ i j, HasCompactSupport (C.principal i j))
    (hdrift : ∀ i, ContDiff ℝ ∞ (C.drift i))
    (hdriftc : ∀ i, HasCompactSupport (C.drift i))
    (hzeroth : ContDiff ℝ ∞ C.zeroth)
    (hzerothc : HasCompactSupport C.zeroth)
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ) :
    ∃ B : ℝ, 0 < B ∧
      (∀ r > 0, ∀ z, |mollifiedValue u ρ r z| ≤ B) ∧
      (∀ r > 0, ∀ z, |mollifiedScalarForcing C u ρ r z| ≤ B) ∧
      (∀ r > 0, ∀ (i : Fin n) (z : Spacetime n),
        |mollifiedFluxForcing C u ρ r i z| ≤ B) := by
  obtain ⟨Mu, hMu⟩ := huc.exists_bound_of_continuous hu
  have hMu' : ∀ y, |u y| ≤ Mu := fun y => by
    simpa only [Real.norm_eq_abs] using hMu y
  have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg (u (0, 0))) (hMu' (0, 0))
  let d : Fin n → Spacetime n → ℝ := fun i y =>
    C.drift i y + ∑ j, spatialDeriv j (C.principal j i) y
  let H : Spacetime n → ℝ := fun y =>
    (∑ i, spatialDeriv i (d i) y) - C.zeroth y
  have hd : ∀ i, ContDiff ℝ ∞ (d i) := by
    intro i
    exact (hdrift i).add (ContDiff.sum (fun j _ =>
      contDiff_spatialDeriv (hprincipal j i) j))
  have hdc : ∀ i, HasCompactSupport (d i) := by
    intro i
    change HasCompactSupport (fun y => C.drift i y +
      ∑ j, spatialDeriv j (C.principal j i) y)
    apply (hdriftc i).add
    change HasCompactSupport (fun y => ∑ j, spatialDeriv j
      (C.principal j i) y)
    rw [show (fun y => ∑ j, spatialDeriv j (C.principal j i) y) =
      ∑ j, spatialDeriv j (C.principal j i) by
        funext y; simp only [Finset.sum_apply]]
    exact HasCompactSupport.finset_sum (fun j _ =>
      hasCompactSupport_spatialDeriv j (hprincipalc j i))
  have hH : ContDiff ℝ ∞ H := by
    exact (ContDiff.sum (fun i _ => contDiff_spatialDeriv (hd i) i)).sub hzeroth
  have hHc : HasCompactSupport H := by
    change HasCompactSupport (fun y =>
      (∑ i, spatialDeriv i (d i) y) - C.zeroth y)
    apply HasCompactSupport.sub
    · change HasCompactSupport (fun y => ∑ i, spatialDeriv i (d i) y)
      rw [show (fun y => ∑ i, spatialDeriv i (d i) y) =
        ∑ i, spatialDeriv i (d i) by
          funext y; simp only [Finset.sum_apply]]
      exact HasCompactSupport.finset_sum (fun i _ =>
        hasCompactSupport_spatialDeriv i (hdc i))
    · exact hzerothc
  obtain ⟨MH, hMH⟩ := hHc.exists_bound_of_continuous hH.continuous
  have hMH' : ∀ y, |H y| ≤ MH := fun y => by
    simpa only [Real.norm_eq_abs] using hMH y
  have hMH0 : 0 ≤ MH := le_trans (abs_nonneg (H (0, 0))) (hMH' (0, 0))
  let A : Fin n → Fin n → ℝ := fun i j =>
    Classical.choose ((hprincipalc i j).exists_bound_of_continuous
      (hprincipal i j).continuous)
  have hA : ∀ i j y, |C.principal i j y| ≤ A i j := by
    intro i j y
    exact (Classical.choose_spec ((hprincipalc i j).exists_bound_of_continuous
      (hprincipal i j).continuous)) y
  let D : Fin n → ℝ := fun i =>
    Classical.choose ((hdc i).exists_bound_of_continuous (hd i).continuous)
  have hD : ∀ i y, |d i y| ≤ D i := by
    intro i y
    exact (Classical.choose_spec ((hdc i).exists_bound_of_continuous
      (hd i).continuous)) y
  have hD0 : ∀ i, 0 ≤ D i := fun i =>
    le_trans (abs_nonneg (d i (0, 0))) (hD i (0, 0))
  have hLex : ∀ i j, ∃ K : ℝ≥0, LipschitzWith K (C.principal i j) := by
    intro i j
    exact ContDiff.lipschitzWith_of_hasCompactSupport
      (hprincipalc i j) (hprincipal i j) (by simp)
  let L : Fin n → Fin n → ℝ≥0 := fun i j => Classical.choose (hLex i j)
  have hL : ∀ i j, LipschitzWith (L i j) (C.principal i j) := by
    intro i j
    exact Classical.choose_spec (hLex i j)
  let I : ℝ := ∫ y : Spacetime n, |ρ y|
  let Mi : Fin n → ℝ := fun i => |D i| * |Mu| * I
  let S : ℝ := ∑ i, (∑ j, ((L i j : ℝ) * |Mu| *
      ((∫ y, ‖y‖ * |fderiv ℝ ρ y (spatialDirection j)|) +
        ‖spatialDirection j‖ * I)) + Mi i)
  let B : ℝ := 1 + |Mu| + |Mu| * I + |MH| * |Mu| * I + 2 * S
  have hnonneg : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro i hi
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro j hj
      positivity
    · dsimp [Mi]
      positivity
  refine ⟨B, by dsimp [B]; positivity, ?_, ?_, ?_⟩
  · intro r hr z
    have h := abs_rescaled_convolution_le hρ hρc hu hMu' hr z
    dsimp [mollifiedValue]
    have hm : 0 ≤ ∫ y : Spacetime n, |ρ y| :=
      integral_nonneg (fun y : Spacetime n => abs_nonneg (ρ y))
    have hMuabs : |Mu| = Mu := abs_of_nonneg hMu0
    have hB0 : 0 ≤ B - Mu * ∫ y, |ρ y| := by
      rw [show (∫ y : Spacetime n, |ρ y|) = I by rfl]
      change 0 ≤ (1 + |Mu| + |Mu| * I + |MH| * |Mu| * I + 2 * S) - Mu * I
      rw [abs_of_nonneg hMu0]
      have hI : 0 ≤ I := by dsimp [I]; positivity
      have hprod : 0 ≤ |MH| * Mu * I := by positivity
      have hmuI : 0 ≤ Mu * I := by positivity
      have hbase : 0 ≤ 1 + Mu := by positivity
      nlinarith [hnonneg, hI, hprod, hmuI, hbase]
    exact h.trans (le_of_sub_nonneg hB0)
  · intro r hr z
    have hHU : Continuous (fun y => H y * u y) := hH.continuous.mul hu
    have h := abs_rescaled_convolution_le hρ hρc hHU
      (M := |MH| * |Mu|) (fun y => by
        simpa only [Pi.mul_apply, abs_mul, abs_of_nonneg hMH0, abs_of_nonneg hMu0] using
          mul_le_mul (hMH' y) (hMu' y) (abs_nonneg _) (by positivity)) hr z
    dsimp [mollifiedScalarForcing]
    have hB0 : 0 ≤ B - (|MH| * |Mu|) * ∫ y, |ρ y| := by
      rw [show (∫ y : Spacetime n, |ρ y|) = I by rfl]
      have hm : 0 ≤ ∫ y : Spacetime n, |ρ y| :=
        integral_nonneg (fun y : Spacetime n => abs_nonneg (ρ y))
      change 0 ≤ (1 + |Mu| + |Mu| * I + |MH| * |Mu| * I + 2 * S) - (|MH| * |Mu|) * I
      have hI : 0 ≤ I := by dsimp [I]; positivity
      have hprod : 0 ≤ |MH| * |Mu| * I := by positivity
      have hmuI : 0 ≤ |Mu| * I := by positivity
      have hbase : 0 ≤ 1 + |Mu| := by positivity
      nlinarith [hnonneg, hI, hprod, hmuI, hbase]
    exact h.trans (le_of_sub_nonneg hB0)
  · intro r hr i z
    have hκ : ContDiff ℝ 1 (rescaledKernel ρ r) :=
      contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))
    have hκc : HasCompactSupport (rescaledKernel ρ r) :=
      (hρc.comp_homeomorph
        (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
    have hcomm (j : Fin n) :
        |C.principal i j z * spatialDeriv j (mollifiedValue u ρ r) z -
          lebesgueConvolution (fun y => spatialDeriv j (rescaledKernel ρ r) y)
            (fun w => C.principal i j w * u w) z +
          lebesgueConvolution (rescaledKernel ρ r)
            (fun w => spatialDeriv j (C.principal i j) w * u w) z| ≤
          (L i j : ℝ) * |Mu| *
            ((∫ y, ‖y‖ * |fderiv ℝ ρ y (spatialDirection j)|) +
              ‖spatialDirection j‖ * ∫ y, |ρ y|) := by
      have hqreg : ContDiff ℝ 1 (C.principal i j) := by
        exact (hprincipal i j).of_le (by simp)
      have hh := abs_mollified_flux_commutator_le volume
        (hL i j) hqreg
          hu hMu' hρ hρc hr
        (spatialDirection j) z
      have hconv : mollifiedValue u ρ r =
          rescaledKernel ρ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by
        exact lebesgueConvolution_eq_convolution _ _
      rw [hconv]
      rw [show spatialDeriv j
          (rescaledKernel ρ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) z =
          ((fun y => fderiv ℝ (rescaledKernel ρ r) y
            (spatialDirection j)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) z by
          exact fderiv_convolution_eq_kernel_derivative volume hu hκ hκc z
            (spatialDirection j)]
      rw [lebesgueConvolution_eq_convolution, lebesgueConvolution_eq_convolution]
      rw [fderiv_convolution_eq_kernel_derivative volume hu hκ hκc] at hh
      simpa only [spatialDeriv, abs_of_nonneg hMu0] using hh
    have hdiCont : Continuous (fun y => d i y * u y) := (hd i).continuous.mul hu
    have hdi := abs_rescaled_convolution_le hρ hρc hdiCont
      (M := |D i| * |Mu|) (fun y => by
        simpa only [abs_mul, abs_of_nonneg (hD0 i), abs_of_nonneg hMu0] using
          mul_le_mul (hD i y) (hMu' y) (abs_nonneg _) (hD0 i)) hr z
    dsimp [mollifiedFluxForcing]
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      (fun j _ => hcomm j)
    have hrow :
        (∑ j, ((L i j : ℝ) * |Mu| *
          ((∫ y, ‖y‖ * |fderiv ℝ ρ y (spatialDirection j)|) +
            ‖spatialDirection j‖ * I)) + Mi i) ≤ S := by
      dsimp [S]
      let R : Fin n → ℝ := fun k =>
        (∑ j, ((L k j : ℝ) * |Mu| *
          ((∫ y, ‖y‖ * |fderiv ℝ ρ y (spatialDirection j)|) +
            ‖spatialDirection j‖ * I)) + Mi k)
      have hR : R i ≤ ∑ k, R k := by
        change R i ≤ ∑ k, R k
        exact Finset.single_le_sum (fun k hk => by
          dsimp [R]
          positivity) (Finset.mem_univ i)
      simpa [R] using hR
    have hcommSum :
        |∑ j, (C.principal i j z * spatialDeriv j
          (mollifiedValue u ρ r) z - lebesgueConvolution
          (fun y => spatialDeriv j (rescaledKernel ρ r) y)
          (fun w => C.principal i j w * u w) z + lebesgueConvolution
          (rescaledKernel ρ r) (fun w => spatialDeriv j (C.principal i j) w * u w) z)| ≤ S := by
      calc
        |∑ j, (C.principal i j z * spatialDeriv j
            (mollifiedValue u ρ r) z - lebesgueConvolution
            (fun y => spatialDeriv j (rescaledKernel ρ r) y)
            (fun w => C.principal i j w * u w) z + lebesgueConvolution
            (rescaledKernel ρ r) (fun w => spatialDeriv j (C.principal i j) w * u w) z)| ≤
            ∑ j, |C.principal i j z * spatialDeriv j
              (mollifiedValue u ρ r) z - lebesgueConvolution
              (fun y => spatialDeriv j (rescaledKernel ρ r) y)
              (fun w => C.principal i j w * u w) z + lebesgueConvolution
              (rescaledKernel ρ r) (fun w => spatialDeriv j (C.principal i j) w * u w) z| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, ((L i j : ℝ) * |Mu| *
            ((∫ y, ‖y‖ * |fderiv ℝ ρ y (spatialDirection j)|) +
              ‖spatialDirection j‖ * I)) := hs
        _ ≤ (∑ j, ((L i j : ℝ) * |Mu| *
            ((∫ y, ‖y‖ * |fderiv ℝ ρ y (spatialDirection j)|) +
              ‖spatialDirection j‖ * I)) + Mi i) :=
          le_add_of_nonneg_right (by positivity)
        _ ≤ S := hrow
    have hdi' :
        |lebesgueConvolution (rescaledKernel ρ r)
          (fun w => d i w * u w) z| ≤ Mi i := by
      simpa [Mi, I] using hdi
    calc
      |-(∑ j, (C.principal i j z * spatialDeriv j
          (mollifiedValue u ρ r) z - lebesgueConvolution
          (fun y => spatialDeriv j (rescaledKernel ρ r) y)
          (fun w => C.principal i j w * u w) z + lebesgueConvolution
          (rescaledKernel ρ r) (fun w => spatialDeriv j (C.principal i j) w * u w) z)) +
          -lebesgueConvolution (rescaledKernel ρ r)
          (fun w => d i w * u w) z| ≤
          |-(∑ j, (C.principal i j z * spatialDeriv j
            (mollifiedValue u ρ r) z - lebesgueConvolution
            (fun y => spatialDeriv j (rescaledKernel ρ r) y)
            (fun w => C.principal i j w * u w) z + lebesgueConvolution
            (rescaledKernel ρ r) (fun w => spatialDeriv j (C.principal i j) w * u w) z))| +
            |-lebesgueConvolution (rescaledKernel ρ r)
              (fun w => d i w * u w) z| := abs_add_le _ _
      _ = |∑ j, (C.principal i j z * spatialDeriv j
            (mollifiedValue u ρ r) z - lebesgueConvolution
            (fun y => spatialDeriv j (rescaledKernel ρ r) y)
            (fun w => C.principal i j w * u w) z + lebesgueConvolution
            (rescaledKernel ρ r) (fun w => spatialDeriv j (C.principal i j) w * u w) z)| +
            |lebesgueConvolution (rescaledKernel ρ r)
              (fun w => d i w * u w) z| := by rw [abs_neg, abs_neg]
      _ ≤ S + Mi i := add_le_add hcommSum hdi'
      _ ≤ B := by
        dsimp [B]
        have hMi : 0 ≤ Mi i := by dsimp [Mi]; positivity
        have hbase : 0 ≤ 1 + |Mu| + |Mu| * I + |MH| * |Mu| * I := by positivity
        have hMiS : Mi i ≤ S := by
          have hrow0 : 0 ≤ ∑ j, ((L i j : ℝ) * |Mu| *
              ((∫ y, ‖y‖ * |fderiv ℝ ρ y (spatialDirection j)|) +
                ‖spatialDirection j‖ * I)) := by positivity
          exact le_trans (le_add_of_nonneg_left hrow0) hrow
        nlinarith [hnonneg, hMiS]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
