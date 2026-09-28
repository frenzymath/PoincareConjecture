import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianFourier
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.RealPeriodicJets










set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative
open scoped ENNReal

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]





theorem realPeriodicJet_heat (k j : ℕ) (hj : j ≤ k) (t : NNReal)
    (u : State (ℤ × Fin 2)) :
    realPeriodicJet (L := L) k j hj (heat (periodicSpectrum L) t u) =
      periodicGaussianHeat (t : ℝ) (realPeriodicJet (L := L) k j hj u) := by
  have hc (n : ℤ) : complexLpRealEquiv.symm (heat (periodicSpectrum L) t u) n =
      (Real.exp (-(2 * Real.pi * (n : ℝ) / L) ^ 2 * (t : ℝ)) : ℂ) *
        complexLpRealEquiv.symm u n := by
    simp only [complexLpRealEquiv_symm_apply, heat_apply]
    change ((Real.exp (-(t : ℝ) * (2 * Real.pi * (n : ℝ) / L) ^ 2) * u (n, 0) : ℝ) : ℂ) +
      Complex.I * ((Real.exp (-(t : ℝ) * (2 * Real.pi * (n : ℝ) / L) ^ 2) * u (n, 1) : ℝ) : ℂ) =
      (Real.exp (-(2 * Real.pi * (n : ℝ) / L) ^ 2 * (t : ℝ)) : ℂ) *
        ((u (n, 0) : ℂ) + Complex.I * (u (n, 1) : ℂ))
    rw [show -(t : ℝ) * (2 * Real.pi * (n : ℝ) / L) ^ 2 =
      -(2 * Real.pi * (n : ℝ) / L) ^ 2 * (t : ℝ) by ring]
    push_cast
    ring
  have hs := (periodicGaussianHeat (t : ℝ)).hasSum
    (weightedFourier_hasSum (L := L)
      ⟨periodicSobolevMoment L k j, (periodicSobolevMoment_bound hj).2⟩
      (complexLpRealEquiv.symm u))
  change HasSum (fun n : ℤ => periodicGaussianHeat (t : ℝ)
      ((periodicSobolevMoment L k j n * complexLpRealEquiv.symm u n) • fourier n))
    (periodicGaussianHeat (t : ℝ)
      (periodicSobolevJet (L := L) k j hj (complexLpRealEquiv.symm u))) at hs
  simp_rw [periodicGaussianHeat_fourier (t : ℝ) t.coe_nonneg] at hs
  have hcoeff (n : ℤ) :
      (periodicSobolevMoment L k j n * complexLpRealEquiv.symm u n) *
          (Real.exp (-(2 * Real.pi * (n : ℝ) / L) ^ 2 * (t : ℝ)) : ℂ) =
        periodicSobolevMoment L k j n *
          complexLpRealEquiv.symm (heat (periodicSpectrum L) t u) n := by
    rw [hc]
    ring
  simp_rw [hcoeff] at hs
  have heq := (weightedFourier_hasSum (L := L)
    ⟨periodicSobolevMoment L k j, (periodicSobolevMoment_bound hj).2⟩
    (complexLpRealEquiv.symm (heat (periodicSpectrum L) t u))).unique hs
  have hre := congrArg (Complex.reCLM.compLeftContinuous ℝ (AddCircle L)) heq
  change realPeriodicJet (L := L) k j hj (heat (periodicSpectrum L) t u) =
    Complex.reCLM.compLeftContinuous ℝ (AddCircle L)
      (periodicGaussianHeat (t : ℝ)
        (periodicSobolevJet (L := L) k j hj (complexLpRealEquiv.symm u))) at hre
  rw [← periodicGaussianHeat_comp] at hre
  exact hre

end PoincareConjecture.M63
