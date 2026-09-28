import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorPeriodicLaplacian

set_option autoImplicit false

open PoincareConjecture.SpectralHeatNative

namespace PoincareConjecture.M63

theorem vectorPeriodic_correctedSource_at_trace
    {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]
    (H V q : State ((ℤ × Fin 2) × ι)) (g : lp (fun _ : ℤ => ℂ) 2)
    (A : AddCircle L → ℝ) (B : AddCircle L → ι → ℝ)
    (M : lp (fun _ : ℤ => ℂ) 2 →L[ℝ]
      State ((ℤ × Fin 2) × ι) →L[ℝ] State ((ℤ × Fin 2) × ι))
    (hV : shiftedBaseMultiplier
      (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) H = V)
    (hg : ∀ x, periodicSobolevJet (L := L) 0 0 (by omega) g x = ((1 - A x : ℝ) : ℂ))
    (hq : ∀ x i, periodicSobolevJet (L := L) 0 0 (by omega)
      (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ q i)) x = (B x i : ℂ))
    (hM : ∀ a, (∀ x, (periodicSobolevJet (L := L) 0 0 (by omega) a x).im = 0) → ∀ u x i,
      vectorPeriodicJet (L := L) 0 0 (by omega) (M a u) x i =
        (periodicSobolevJet (L := L) 0 0 (by omega) a x).re *
          vectorPeriodicJet (L := L) 0 0 (by omega) u x i) :
    ∀ x i, vectorPeriodicJet (L := L) 0 0 (by omega)
        (M g (H - shiftedBaseMultiplier
          (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) V) + q) x i =
      (A x - 1) * vectorPeriodicJet (L := L) 2 2 (by omega) H x i + B x i := by
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let J := shiftedBaseMultiplier lambda
  have hJV : J V = scaleDecode lambda 2 H := by
    rw [← hV]
    apply lp.ext
    funext i
    change (shiftedBaseMultiplier lambda (shiftedBaseMultiplier lambda H)) i = _
    simp only [shiftedBaseMultiplier, multiplier_apply, scaleDecode_apply, scaleWeight,
      one_div, pow_two, mul_inv]
    ring
  have hreal : ∀ x, (periodicSobolevJet (L := L) 0 0 (by omega) g x).im = 0 := by
    intro x
    rw [hg, Complex.ofReal_im]
  intro x i
  have hlower : vectorPeriodicJet (L := L) 0 0 (by omega) q x i = B x i :=
    congrArg Complex.re (hq x i)
  have hsecond := congrArg (fun f : C(AddCircle L, ι → ℝ) => f x i)
    (vectorPeriodicJet_laplacian (L := L) H)
  rw [← hJV] at hsecond
  change vectorPeriodicJet (L := L) 2 2 (by omega) H x i =
    -vectorPeriodicJet (L := L) 0 0 (by omega) (H - J V) x i at hsecond
  simp only [map_add, ContinuousMap.add_apply, Pi.add_apply, hM _ hreal, hg,
    Complex.ofReal_re, hlower, hsecond]
  ring

end PoincareConjecture.M63
