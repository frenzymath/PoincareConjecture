import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorPeriodicH1Coefficients
import PoincareConjecture.Proofs.M03.Existence.SpectralShiftedNative

set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]

theorem vectorPeriodicJet_laplacian (H : State ((ℤ × Fin 2) × ι)) :
    vectorPeriodicJet (L := L) 2 2 (by omega) H =
      -vectorPeriodicJet (L := L) 0 0 (by omega)
        (H - scaleDecode (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) 2 H) := by
  have hm (n : ℤ) : periodicSobolevMoment L 2 2 n =
      -(periodicSobolevMoment L 0 0 n - periodicSobolevMoment L 2 0 n) := by
    let omega : ℝ := 2 * Real.pi * (n : ℝ) / L
    let rho : ℝ := Real.sqrt (1 + omega ^ 2)
    have hrho : rho ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 1 + omega ^ 2)).ne'
    have hc : (rho : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrho
    have hs : (rho : ℂ) ^ 2 = 1 + (omega : ℂ) ^ 2 := by
      exact_mod_cast (Real.sq_sqrt (by positivity : 0 ≤ 1 + omega ^ 2))
    change (Complex.I * (omega : ℂ)) ^ 2 / (rho : ℂ) ^ 3 =
      -(1 / (rho : ℂ) ^ 1 - 1 / (rho : ℂ) ^ 3)
    rw [mul_pow, Complex.I_sq, pow_one]
    field_simp
    linear_combination hs
  have hscalar (u : lp (fun _ : ℤ => ℂ) 2) :
      periodicSobolevJet (L := L) 2 2 (by omega) u =
        -(periodicSobolevJet (L := L) 0 0 (by omega) u -
          periodicSobolevJet (L := L) 2 0 (by omega) u) := by
    have h22 := weightedFourier_hasSum (L := L)
      ⟨periodicSobolevMoment L 2 2, (periodicSobolevMoment_bound (by omega)).2⟩ u
    have h00 := weightedFourier_hasSum (L := L)
      ⟨periodicSobolevMoment L 0 0, (periodicSobolevMoment_bound (by omega)).2⟩ u
    have h20 := weightedFourier_hasSum (L := L)
      ⟨periodicSobolevMoment L 2 0, (periodicSobolevMoment_bound (by omega)).2⟩ u
    apply h22.unique
    apply (h00.sub h20).neg.congr_fun
    intro n
    change (periodicSobolevMoment L 2 2 n * u n) • fourier n =
      -((periodicSobolevMoment L 0 0 n * u n) • fourier n -
        (periodicSobolevMoment L 2 0 n * u n) • fourier n)
    rw [hm]
    simp only [neg_mul, sub_mul, neg_smul, sub_smul]
  rw [map_sub, vectorPeriodicJet_scaleDecode]
  ext x i
  change (periodicSobolevJet (L := L) 2 2 (by omega)
      (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ H i)) x).re =
    -((periodicSobolevJet (L := L) 0 0 (by omega)
      (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ H i)) x).re -
      (periodicSobolevJet (L := L) 2 0 (by omega)
        (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ H i)) x).re)
  have h := congrArg (fun f : C(AddCircle L, ℂ) => (f x).re)
    (hscalar (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ H i)))
  simpa only [ContinuousMap.neg_apply, ContinuousMap.sub_apply, Complex.neg_re, Complex.sub_re]
    using h

theorem vectorPeriodic_correctedSource {P : Type*}
    (A : P → ((Fin 2 × ι) → ℝ) → ℝ) (R : P → ((Fin 2 × ι) → ℝ) → (ι → ℝ))
    (G : P → State ((ℤ × Fin 2) × ι) → lp (fun _ : ℤ => ℂ) 2)
    (Q : P → State ((ℤ × Fin 2) × ι) → State ((ℤ × Fin 2) × ι))
    (M : lp (fun _ : ℤ => ℂ) 2 →L[ℝ]
      State ((ℤ × Fin 2) × ι) →L[ℝ] State ((ℤ × Fin 2) × ι))
    (hG : ∀ p u x, periodicSobolevJet (L := L) 0 0 (by omega) (G p u) x =
      ((1 - A p (fun j : Fin 2 × ι =>
        vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) : ℝ) : ℂ))
    (hQ : ∀ p u x i, periodicSobolevJet (L := L) 0 0 (by omega)
      (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (Q p u) i)) x =
      (R p (fun j : Fin 2 × ι => vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) i : ℂ))
    (hM : ∀ a, (∀ x, (periodicSobolevJet (L := L) 0 0 (by omega) a x).im = 0) → ∀ u x i,
      vectorPeriodicJet (L := L) 0 0 (by omega) (M a u) x i =
        (periodicSobolevJet (L := L) 0 0 (by omega) a x).re *
          vectorPeriodicJet (L := L) 0 0 (by omega) u x i)
    (p : P) (H : State ((ℤ × Fin 2) × ι)) :
    let J := shiftedBaseMultiplier (fun q : (ℤ × Fin 2) × ι => periodicSpectrum L q.1)
    let v := J H
    let U := J v
    ∀ x i, vectorPeriodicJet (L := L) 0 0 (by omega)
        (M (G p v) H - M (G p v) U + Q p v) x i =
      (A p (fun j : Fin 2 × ι => vectorPeriodicJet (L := L) 1 j.1 (by omega) v x j.2) - 1) *
        vectorPeriodicJet (L := L) 2 2 (by omega) H x i +
      R p (fun j : Fin 2 × ι => vectorPeriodicJet (L := L) 1 j.1 (by omega) v x j.2) i := by
  dsimp only
  let lambda := fun q : (ℤ × Fin 2) × ι => periodicSpectrum L q.1
  let J := shiftedBaseMultiplier lambda
  let v := J H
  let U := J v
  have hU : U = scaleDecode lambda 2 H := by
    apply lp.ext
    funext i
    change (shiftedBaseMultiplier lambda (shiftedBaseMultiplier lambda H)) i = _
    simp only [shiftedBaseMultiplier, multiplier_apply, scaleDecode_apply, scaleWeight,
      one_div, pow_two, mul_inv]
    ring
  have hreal : ∀ x, (periodicSobolevJet (L := L) 0 0 (by omega) (G p v) x).im = 0 := by
    intro x
    rw [hG, Complex.ofReal_im]
  intro x i
  change vectorPeriodicJet (L := L) 0 0 (by omega)
      (M (G p v) H - M (G p v) U + Q p v) x i = _
  have hlower : vectorPeriodicJet (L := L) 0 0 (by omega) (Q p v) x i =
      R p (fun j : Fin 2 × ι => vectorPeriodicJet (L := L) 1 j.1 (by omega) v x j.2) i :=
    congrArg Complex.re (hQ p v x i)
  have hsecond := congrArg (fun f : C(AddCircle L, ι → ℝ) => f x i)
    (vectorPeriodicJet_laplacian (L := L) H)
  rw [← hU, map_sub] at hsecond
  change vectorPeriodicJet (L := L) 2 2 (by omega) H x i =
    -(vectorPeriodicJet (L := L) 0 0 (by omega) H x i -
      vectorPeriodicJet (L := L) 0 0 (by omega) U x i) at hsecond
  simp only [map_add, map_sub, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    Pi.add_apply, Pi.sub_apply, hM _ hreal, hG, Complex.ofReal_re, hlower, hsecond]
  ring

end PoincareConjecture.M63
