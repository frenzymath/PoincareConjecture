import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorPeriodicJets
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicInitialCoordinates









set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative

namespace PoincareConjecture.M63




theorem exists_vectorPeriodic_initialCoordinates {L : ℝ} [Fact (0 < L)]
    {ι : Type*} [Fintype ι] (f : C(AddCircle L, ι → ℝ))
    (hf : ContDiff ℝ 2 (fun x : ℝ => f (x : AddCircle L))) :
    let fi : ι → C(AddCircle L, ℝ) := fun i =>
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).compLeftContinuous ℝ (AddCircle L) f
    ∃ w : State ((ℤ × Fin 2) × ι),
      (∀ i (n : ℤ), complexLpRealEquiv.symm (lpFinitePiEquiv ℝ w i) n =
        ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
          fourierCoeff (Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L) (fi i)) n) ∧
      vectorPeriodicJet (L := L) 1 0 (by omega) w = f ∧
      vectorPeriodicJet (L := L) 0 0 (by omega)
        (shiftedBaseMultiplier (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) w) = f := by
  classical
  let fi : ι → C(AddCircle L, ℝ) := fun i =>
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).compLeftContinuous ℝ (AddCircle L) f
  have hfi (i : ι) : ContDiff ℝ 2 (fun x : ℝ => fi i (x : AddCircle L)) :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.comp hf
  choose w hw hrec hrec0 using fun i => exists_realPeriodic_initialCoordinates (fi i) (hfi i)
  refine ⟨(lpFinitePiEquiv ℝ).symm w, ?_, ?_, ?_⟩
  · intro i n
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hw i n
  · ext x i
    change realPeriodicJet (L := L) 1 0 (by omega)
      (lpFinitePiEquiv ℝ ((lpFinitePiEquiv ℝ).symm w) i) x = f x i
    rw [ContinuousLinearEquiv.apply_symm_apply, hrec]
    rfl
  · have hsplit (u : State ((ℤ × Fin 2) × ι)) (i : ι) :
        lpFinitePiEquiv ℝ
            (shiftedBaseMultiplier (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) u) i =
          shiftedBaseMultiplier (periodicSpectrum L) (lpFinitePiEquiv ℝ u i) := by
      apply lp.ext
      funext p
      rfl
    ext x i
    change realPeriodicJet (L := L) 0 0 (by omega)
      (lpFinitePiEquiv ℝ
        (shiftedBaseMultiplier (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1)
          ((lpFinitePiEquiv ℝ).symm w)) i) x = f x i
    rw [hsplit, ContinuousLinearEquiv.apply_symm_apply, hrec0]
    rfl

end PoincareConjecture.M63
