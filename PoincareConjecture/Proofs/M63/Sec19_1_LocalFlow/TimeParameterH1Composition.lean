import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1FiniteComposition
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorPeriodicH1Coefficients











set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]




theorem exists_timeParameter_scalarH1_composition (k : ℕ)
    (f : ℝ × ((Fin 2 × ι) → ℝ) → ℝ) (hf : ContDiff ℝ (k + 1) f) :
    ∃ G : ℝ × State ((ℤ × Fin 2) × ι) → lp (fun _ : ℤ => ℂ) 2,
      ContDiff ℝ k G ∧ ∀ t u x,
        periodicSobolevJet (L := L) 0 0 (by omega) (G (t, u)) x =
          (f (t, fun j : Fin 2 × ι =>
            vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) : ℂ) := by
  classical
  let J := Fin 2 × ι
  let H := lp (fun _ : ℤ => ℂ) 2
  let S := State ((ℤ × Fin 2) × ι)
  let R : (Option J → ℂ) →L[ℝ] ℝ × (J → ℝ) :=
    (Complex.reCLM.comp (ContinuousLinearMap.proj none)).prod
      (ContinuousLinearMap.pi (fun j => Complex.reCLM.comp (ContinuousLinearMap.proj (some j))))
  let Φ : (Option J → ℂ) → ℂ := fun z => f (R z)
  have hΦ : ContDiff ℝ (k + 1) Φ := Complex.ofRealCLM.contDiff.comp (hf.comp R.contDiff)
  let X := vectorPeriodicH1JetCoordinates (L := L) (ι := ι)
  let C : ℝ →L[ℝ] H :=
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).restrictScalars ℝ).comp
      Complex.ofRealCLM
  let Z : ℝ × S →L[ℝ] (Option J → H) := ContinuousLinearMap.pi (fun j =>
    match j with
    | none => C.comp (ContinuousLinearMap.fst ℝ ℝ S)
    | some i => (ContinuousLinearMap.proj i).comp (X.comp (ContinuousLinearMap.snd ℝ ℝ S)))
  obtain ⟨G, hG, hdecode⟩ := exists_periodicH1_finite_composition (L := L) k Φ hΦ
  refine ⟨G ∘ Z, hG.comp Z.contDiff, ?_⟩
  intro t u x
  rw [Function.comp_apply, hdecode]
  change (f (R (periodicH1VectorDecoder (L := L) (Option J) (Z (t, u)) x)) : ℂ) = _
  apply congrArg (fun z => (f z : ℂ))
  apply Prod.ext
  · change (periodicSobolevJet (L := L) 0 0 (by omega) (lp.single 2 0 (t : ℂ)) x).re = t
    rw [(periodicH1Decoder_single (L := L) 0 (t : ℂ)).1]
    simp
  · funext j
    exact (vectorPeriodicH1JetCoordinates_spec (L := L) u).2.2 j x




theorem exists_timeParameter_vectorH1_composition (k : ℕ)
    (f : ℝ × ((Fin 2 × ι) → ℝ) → (ι → ℝ)) (hf : ContDiff ℝ (k + 1) f) :
    ∃ G : ℝ × State ((ℤ × Fin 2) × ι) → State ((ℤ × Fin 2) × ι),
      ContDiff ℝ k G ∧ ∀ t u x i,
        periodicSobolevJet (L := L) 0 0 (by omega)
          (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (G (t, u)) i)) x =
          (f (t, fun j : Fin 2 × ι =>
            vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) i : ℂ) := by
  classical
  have hcomponent (i : ι) := exists_timeParameter_scalarH1_composition (L := L) k
    (fun z => f z i) ((contDiff_apply ℝ ℝ i).comp hf)
  choose G hG hdecode using hcomponent
  let S := lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ
  let R := complexLpRealEquiv (ι := ℤ)
  refine ⟨fun z => S.symm (fun i => R (G i z)), ?_, ?_⟩
  · exact S.symm.contDiff.comp (contDiff_pi.mpr (fun i => R.contDiff.comp (hG i)))
  · intro t u x i
    change periodicSobolevJet (L := L) 0 0 (by omega)
      (R.symm (S (S.symm (fun i => R (G i (t, u)))) i)) x = _
    rw [S.apply_symm_apply, R.symm_apply_apply]
    exact hdecode i t u x

end PoincareConjecture.M63
