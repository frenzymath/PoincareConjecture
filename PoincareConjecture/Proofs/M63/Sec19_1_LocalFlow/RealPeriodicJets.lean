import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSobolevJets
import PoincareConjecture.Proofs.M63.Mathlib.ComplexLpRealification
import PoincareConjecture.Proofs.M03.Existence.SpectralScaleNative

set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative
open scoped ENNReal

namespace PoincareConjecture.M63

noncomputable def periodicSpectrum (L : ℝ) (p : ℤ × Fin 2) : NNReal :=
  ⟨(2 * Real.pi * (p.1 : ℝ) / L) ^ 2, sq_nonneg _⟩

variable {L : ℝ} [Fact (0 < L)]

noncomputable def realPeriodicJet (k j : ℕ) (hj : j ≤ k) :
    State (ℤ × Fin 2) →L[ℝ] C(AddCircle L, ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ (AddCircle L)).comp
    (((periodicSobolevJet (L := L) k j hj).restrictScalars ℝ).comp
      complexLpRealEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem norm_realPeriodicJet_le (k j : ℕ) (hj : j ≤ k) (u : State (ℤ × Fin 2)) :
    ‖realPeriodicJet (L := L) k j hj u‖ ≤
      ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
        memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖ * ‖u‖ := by
  have hnorm : ‖realPeriodicJet (L := L) k j hj u‖ ≤
      ‖periodicSobolevJet (L := L) k j hj (complexLpRealEquiv.symm u)‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    exact (Complex.abs_re_le_norm _).trans (ContinuousMap.norm_coe_le_norm _ x)
  exact hnorm.trans (by simpa using
    norm_periodicSobolevJet_le (L := L) k j hj (complexLpRealEquiv.symm u))

theorem hasDerivAt_realPeriodicJet {k j : ℕ} (hj : j < k)
    (u : State (ℤ × Fin 2)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => realPeriodicJet (L := L) k j hj.le u (y : AddCircle L))
      (realPeriodicJet (L := L) k (j + 1) hj u (x : AddCircle L)) x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_periodicSobolevJet hj (complexLpRealEquiv.symm u) x)

theorem realPeriodicJet_regular (k : ℕ) (u : State (ℤ × Fin 2)) :
    let U := fun x : ℝ => realPeriodicJet (L := L) k 0 (Nat.zero_le k) u (x : AddCircle L)
    Function.Periodic U L ∧ ContDiff ℝ k U ∧
      ∀ j (hj : j ≤ k), iteratedDeriv j U =
        fun x : ℝ => realPeriodicJet (L := L) k j hj u (x : AddCircle L) := by
  dsimp only
  have heq : ∀ j (hj : j ≤ k),
      iteratedDeriv j (fun x : ℝ =>
        realPeriodicJet (L := L) k 0 (Nat.zero_le k) u (x : AddCircle L)) =
        fun x : ℝ => realPeriodicJet (L := L) k j hj u (x : AddCircle L) := by
    intro j
    induction j with
    | zero => intro hj; rw [iteratedDeriv_zero]
    | succ j ih =>
        intro hj
        have hj' : j < k := Nat.lt_of_succ_le hj
        rw [iteratedDeriv_succ, ih hj'.le]
        funext x
        exact (hasDerivAt_realPeriodicJet hj' u x).deriv
  refine ⟨?_, contDiff_nat_iff_iteratedDeriv.mpr ⟨?_, ?_⟩, heq⟩
  · intro x
    dsimp only
    rw [coe_add_period]
  · intro j hj
    rw [heq j hj]
    exact (realPeriodicJet (L := L) k j hj u).continuous.comp
      (AddCircle.continuous_mk' L)
  · intro j hj
    rw [heq j hj.le]
    exact fun x => (hasDerivAt_realPeriodicJet hj u x).differentiableAt

omit [Fact (0 < L)] in

theorem complexLpRealEquiv_scaleDecode (l : ℕ) (u : State (ℤ × Fin 2)) (n : ℤ) :
    complexLpRealEquiv.symm (scaleDecode (periodicSpectrum L) l u) n =
      (((Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) ^ l)⁻¹ : ℝ) : ℂ) *
        complexLpRealEquiv.symm u n := by
  simp only [complexLpRealEquiv_symm_apply, scaleDecode_apply]
  let a := (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) ^ l)⁻¹
  change ((a * u (n, 0) : ℝ) : ℂ) + Complex.I * ((a * u (n, 1) : ℝ) : ℂ) =
    (a : ℂ) * ((u (n, 0) : ℂ) + Complex.I * (u (n, 1) : ℂ))
  simp only [Complex.ofReal_mul]
  ring

theorem realPeriodicJet_scaleDecode (k j l : ℕ) (hj : j ≤ k)
    (u : State (ℤ × Fin 2)) :
    realPeriodicJet (L := L) k j hj (scaleDecode (periodicSpectrum L) l u) =
      realPeriodicJet (L := L) (k + l) j (hj.trans (Nat.le_add_right k l)) u := by
  have hc (n : ℤ) :
      periodicSobolevMoment L k j n *
          complexLpRealEquiv.symm (scaleDecode (periodicSpectrum L) l u) n =
        periodicSobolevMoment L (k + l) j n * complexLpRealEquiv.symm u n := by
    rw [complexLpRealEquiv_scaleDecode]
    simp only [periodicSobolevMoment, Complex.ofReal_inv, Complex.ofReal_pow]
    rw [show k + l + 1 = (k + 1) + l by omega, pow_add]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hs := weightedFourier_hasSum (L := L)
    ⟨periodicSobolevMoment L k j, (periodicSobolevMoment_bound hj).2⟩
    (complexLpRealEquiv.symm (scaleDecode (periodicSpectrum L) l u))
  change HasSum (fun n : ℤ => (periodicSobolevMoment L k j n *
      complexLpRealEquiv.symm (scaleDecode (periodicSpectrum L) l u) n) • fourier n)
    (periodicSobolevJet (L := L) k j hj
      (complexLpRealEquiv.symm (scaleDecode (periodicSpectrum L) l u))) at hs
  simp_rw [hc] at hs
  have heq := hs.unique (weightedFourier_hasSum (L := L)
    ⟨periodicSobolevMoment L (k + l) j,
      (periodicSobolevMoment_bound (hj.trans (Nat.le_add_right k l))).2⟩
    (complexLpRealEquiv.symm u))
  exact congrArg (Complex.reCLM.compLeftContinuous ℝ (AddCircle L)) heq

end PoincareConjecture.M63
