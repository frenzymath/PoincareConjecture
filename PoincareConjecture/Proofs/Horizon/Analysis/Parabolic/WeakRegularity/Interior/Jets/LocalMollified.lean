




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.MollifiedForcingBounds
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.UniformCutoffEnergy









open Set MeasureTheory Filter
open Poincare.Analysis.Convolution
open scoped ContDiff Topology Convolution

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

local instance {n : ℕ} : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

theorem exists_uniform_local_mollified_cutoff_gradient_bound
    {n : ℕ} {C : Coefficients n} {u ρ χ : Spacetime n → ℝ}
    {U : Set (Spacetime n)} {κ : ℝ}
    (hprincipal : ∀ i j, ContDiff ℝ ∞ (C.principal i j))
    (hprincipalc : ∀ i j, HasCompactSupport (C.principal i j))
    (hdrift : ∀ i, ContDiff ℝ ∞ (C.drift i))
    (hdriftc : ∀ i, HasCompactSupport (C.drift i))
    (hzeroth : ContDiff ℝ ∞ C.zeroth)
    (hzerothc : HasCompactSupport C.zeroth)
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hw : WeakSolutionOn C u U)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hκ : 0 < κ)
    (hEll : ∀ z ∈ tsupport χ, ∀ ξ : Euclid n,
      κ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, C.principal i j z * ξ i * ξ j) :
    ∃ B : ℝ, 0 < B ∧ ∀ r > 0,
      (∀ z ∈ tsupport χ,
        tsupport (translatedKernel (rescaledKernel ρ r) z) ⊆ U) →
      (∫ z, ∑ i, (χ z * spatialDeriv i (mollifiedValue u ρ r) z) ^ 2) ≤ B := by
  obtain ⟨M, hMpos, hMval, hMscalar, hMflux⟩ :=
    exists_uniform_mollified_forcing_bounds hprincipal hprincipalc hdrift hdriftc
      hzeroth hzerothc hu huc (hρ.of_le (by simp)) hρc
  obtain ⟨B, hBpos, hB⟩ := exists_uniform_cutoff_gradient_bound (M := M)
    hκ hMpos.le hprincipal hχ hχc hEll
  refine ⟨B, hBpos, ?_⟩
  intro r hr hs
  let η : Spacetime n → ℝ := rescaledKernel ρ r
  have hη : ContDiff ℝ ∞ η :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))
  have hηc : HasCompactSupport η :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  have hconv {k g : Spacetime n → ℝ} (hk : ContDiff ℝ ∞ k)
      (hkc : HasCompactSupport k) (hg : Continuous g) :
      ContDiff ℝ ∞ (lebesgueConvolution k g) :=
    contDiff_lebesgueConvolution hg.locallyIntegrable hk hkc
  have hval : ContDiff ℝ ∞ (mollifiedValue u ρ r) :=
    hconv hη hηc hu
  let d : Fin n → Spacetime n → ℝ := fun i y =>
    C.drift i y + ∑ j, spatialDeriv j (C.principal j i) y
  have hd : ∀ i, ContDiff ℝ ∞ (d i) := fun i =>
    (hdrift i).add (ContDiff.sum (fun j _ =>
      contDiff_spatialDeriv (hprincipal j i) j))
  have hH : ContDiff ℝ ∞ (fun y =>
      (∑ i, spatialDeriv i (d i) y) - C.zeroth y) :=
    (ContDiff.sum (fun i _ => contDiff_spatialDeriv (hd i) i)).sub hzeroth
  have hscalar : ContDiff ℝ ∞ (mollifiedScalarForcing C u ρ r) :=
    hconv hη hηc (hH.continuous.mul hu)
  have hflux : ∀ i, ContDiff ℝ ∞ (mollifiedFluxForcing C u ρ r i) := by
    intro i
    have hterm (j : Fin n) : ContDiff ℝ ∞ (fun z =>
        C.principal i j z * spatialDeriv j (mollifiedValue u ρ r) z -
          lebesgueConvolution (fun y => spatialDeriv j η y)
            (fun w => C.principal i j w * u w) z +
          lebesgueConvolution η
            (fun w => spatialDeriv j (C.principal i j) w * u w) z) :=
      (((hprincipal i j).mul (contDiff_spatialDeriv hval j)).sub
        (hconv (contDiff_spatialDeriv hη j)
          (hηc.fderiv_apply ℝ (spatialDirection j))
          ((hprincipal i j).continuous.mul hu))).add
        (hconv hη hηc
          ((contDiff_spatialDeriv (hprincipal i j) j).continuous.mul hu))
    exact (ContDiff.sum (fun j _ => hterm j)).neg.sub
      (hconv hη hηc ((hd i).continuous.mul hu))
  apply hB hval hscalar hflux
  · exact fun z _ => hMval r hr z
  · exact fun z _ => hMscalar r hr z
  · exact fun i z _ => hMflux r hr i z
  · intro z hz
    exact WeakSolutionOn.mollified_divergence_equation hprincipal hdrift hzeroth hu hw
      hη hηc (hs z hz)

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
