import PoincareConjecture.Proofs.M63.Mathlib.CompactPartialDerivativeBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.RealGeometricH1Composition
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.TimeParameterH1Composition










set_option autoImplicit false

open PoincareConjecture.SpectralHeatNative

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]




theorem exists_compact_scalarH1_coefficient
    (f : ℝ × ((Fin 2 × ι) → ℝ) → ℝ)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∃ G : ℝ × State ((ℤ × Fin 2) × ι) → lp (fun _ : ℤ => ℂ) 2,
      ContDiff ℝ 1 G ∧
      (∀ t u x, periodicSobolevJet (L := L) 0 0 (by omega) (G (t, u)) x =
        (f (t, fun j : Fin 2 × ι =>
          vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) : ℂ)) ∧
      ∀ R : ℝ, 0 ≤ R → ∃ K : NNReal, ∀ t u v, ‖u‖ ≤ R → ‖v‖ ≤ R →
        ‖G (t, u) - G (t, v)‖ ≤ K * ‖u - v‖ := by
  let J := Fin 2 × ι
  let f1 := fun t z => (fderiv ℝ f (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ (J → ℝ))
  obtain ⟨hfc, A, B, hfd, hfL⟩ := exists_uniform_partial_derivative_bounds hf hc
  obtain ⟨D, _hDcont, hDdecode, hDtame⟩ := exists_realScalarH1_composition (L := L)
    (fun t z => f (t, z)) f1 hf.continuous hfc (fun t z => (hfd t z).1)
    A.coe_nonneg B.coe_nonneg (fun t z => (hfd t z).2)
    (fun t z w => by simpa only [dist_eq_norm] using (hfL t).dist_le_mul z w)
  obtain ⟨G, hG, hGdecode⟩ := exists_timeParameter_scalarH1_composition (L := L) 1 f
    (by simpa only [Nat.cast_one, one_add_one_eq_two] using hf)
  have hGD (t : ℝ) (u : State ((ℤ × Fin 2) × ι)) : G (t, u) = D t u := by
    apply periodicH1Decoder_injective (L := L)
    apply ContinuousMap.ext
    intro x
    rw [hGdecode, hDdecode]
  refine ⟨G, hG, hGdecode, ?_⟩
  intro R hR
  let d := ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
    memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖
  let c : ℝ := 4 * (1 + (Fintype.card J : ℝ))
  have hK : 0 ≤ c * ((A : ℝ) + B * d * R) := by dsimp [c, d]; positivity
  refine ⟨⟨c * ((A : ℝ) + B * d * R), hK⟩, ?_⟩
  intro t u v _hu hv
  rw [hGD, hGD]
  apply (hDtame t u v).trans
  change c * ((A : ℝ) + B * d * ‖v‖) * ‖u - v‖ ≤
    c * ((A : ℝ) + B * d * R) * ‖u - v‖
  dsimp only [c, d]
  gcongr




theorem exists_compact_vectorH1_coefficient
    (f : ℝ × ((Fin 2 × ι) → ℝ) → (ι → ℝ))
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∃ G : ℝ × State ((ℤ × Fin 2) × ι) → State ((ℤ × Fin 2) × ι),
      ContDiff ℝ 1 G ∧
      (∀ t u x i, periodicSobolevJet (L := L) 0 0 (by omega)
        (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (G (t, u)) i)) x =
        (f (t, fun j : Fin 2 × ι =>
          vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) i : ℂ)) ∧
      ∀ R : ℝ, 0 ≤ R → ∃ K : NNReal, ∀ t u v, ‖u‖ ≤ R → ‖v‖ ≤ R →
        ‖G (t, u) - G (t, v)‖ ≤ K * ‖u - v‖ := by
  let J := Fin 2 × ι
  let f1 := fun t z => (fderiv ℝ f (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ (J → ℝ))
  obtain ⟨hfc, A, B, hfd, hfL⟩ := exists_uniform_partial_derivative_bounds hf hc
  obtain ⟨D, _hDcont, hDdecode, hDtame⟩ := exists_realVectorH1_composition (L := L)
    (fun t z => f (t, z)) f1 hf.continuous hfc (fun t z => (hfd t z).1)
    A.coe_nonneg B.coe_nonneg (fun t z => (hfd t z).2)
    (fun t z w => by simpa only [dist_eq_norm] using (hfL t).dist_le_mul z w)
  obtain ⟨G, hG, hGdecode⟩ := exists_timeParameter_vectorH1_composition (L := L) 1 f
    (by simpa only [Nat.cast_one, one_add_one_eq_two] using hf)
  have hGD (t : ℝ) (u : State ((ℤ × Fin 2) × ι)) : G (t, u) = D t u := by
    apply (lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ).injective
    funext i
    apply complexLpRealEquiv.symm.injective
    apply periodicH1Decoder_injective (L := L)
    apply ContinuousMap.ext
    intro x
    rw [hGdecode, hDdecode]
  refine ⟨G, hG, hGdecode, ?_⟩
  intro R hR
  let d := ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
    memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖
  let c : ℝ := (1 + (Fintype.card ι : ℝ)) * (4 * (1 + (Fintype.card J : ℝ)))
  have hK : 0 ≤ c * ((A : ℝ) + B * d * R) := by dsimp [c, d]; positivity
  refine ⟨⟨c * ((A : ℝ) + B * d * R), hK⟩, ?_⟩
  intro t u v _hu hv
  rw [hGD, hGD]
  apply (hDtame t u v).trans
  change c * ((A : ℝ) + B * d * ‖v‖) * ‖u - v‖ ≤
    c * ((A : ℝ) + B * d * R) * ‖u - v‖
  dsimp only [c, d]
  gcongr

end PoincareConjecture.M63
