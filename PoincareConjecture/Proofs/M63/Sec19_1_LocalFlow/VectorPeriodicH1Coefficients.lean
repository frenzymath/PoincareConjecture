import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH2JetCoordinates
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1Product
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorPeriodicJets

set_option autoImplicit false

open PoincareConjecture.SpectralHeatNative

namespace PoincareConjecture.M63

variable {L : ℝ} {ι : Type*} [Fintype ι]

noncomputable def vectorPeriodicH1JetCoordinates :
    State ((ℤ × Fin 2) × ι) →L[ℝ] ((Fin 2 × ι) → lp (fun _ : ℤ => ℂ) 2) :=
  ContinuousLinearMap.pi (fun p : Fin 2 × ι =>
    ((periodicH2JetCoordinates (L := L) p.1 (by omega)).restrictScalars ℝ).comp
      (complexLpRealEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ContinuousLinearMap.proj p.2).comp
          (lpFinitePiEquiv ℝ).toContinuousLinearMap)))

variable [Fact (0 < L)]

theorem vectorPeriodicH1JetCoordinates_spec (u : State ((ℤ × Fin 2) × ι)) :
    ‖vectorPeriodicH1JetCoordinates (L := L) u‖ ≤ ‖u‖ ∧
      (∀ p : Fin 2 × ι,
        periodicSobolevJet (L := L) 0 0 (by omega)
          (vectorPeriodicH1JetCoordinates (L := L) u p) =
        periodicSobolevJet (L := L) 1 p.1 (by omega)
          (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ u p.2))) ∧
      ∀ (p : Fin 2 × ι) (x : AddCircle L),
        (periodicSobolevJet (L := L) 0 0 (by omega)
          (vectorPeriodicH1JetCoordinates (L := L) u p) x).re =
        vectorPeriodicJet (L := L) 1 p.1 (by omega) u x p.2 := by
  have hc (p : Fin 2 × ι) := periodicH2JetCoordinates_spec (L := L)
    p.1 (by omega) (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ u p.2))
  refine ⟨?_, fun p => (hc p).2, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg u)]
    intro p
    exact (hc p).1.trans (by
      rw [LinearIsometryEquiv.norm_map]
      exact (norm_le_pi_norm (lpFinitePiEquiv ℝ u) p.2).trans (norm_lpFinitePiEquiv_le ℝ u))
  · intro p x
    change (periodicSobolevJet (L := L) 0 0 (by omega)
      (periodicH2JetCoordinates (L := L) p.1 (by omega)
        (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ u p.2))) x).re = _
    rw [(hc p).2]
    rfl

theorem exists_vectorPeriodicH1_product :
    let D := periodicSobolevJet (L := L) 0 0 (by omega)
    let Z := fun (u : State ((ℤ × Fin 2) × ι)) (i : ι) =>
      complexLpRealEquiv.symm (lpFinitePiEquiv ℝ u i)
    ∃ M : lp (fun _ : ℤ => ℂ) 2 →L[ℝ]
        State ((ℤ × Fin 2) × ι) →L[ℝ] State ((ℤ × Fin 2) × ι),
      (∀ a u i, D (Z (M a u) i) = D a * D (Z u i)) ∧
      ‖M‖ ≤ (1 + (Fintype.card ι : ℝ)) * 4 *
        ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
          memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖ ∧
      ∀ a, (∀ x, (D a x).im = 0) → ∀ u x i,
        vectorPeriodicJet (L := L) 0 0 (by omega) (M a u) x i =
          (D a x).re * vectorPeriodicJet (L := L) 0 0 (by omega) u x i := by
  let H := lp (fun _ : ℤ => ℂ) 2
  let S := lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ
  let R := complexLpRealEquiv (ι := ℤ)
  let D := periodicSobolevJet (L := L) 0 0 (by omega)
  let Z := fun (u : State ((ℤ × Fin 2) × ι)) (i : ι) => R.symm (S u i)
  let d := ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
    memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖
  obtain ⟨B, hB, hBnorm⟩ := exists_periodicH1_product (L := L)
  let BR := B.bilinearRestrictScalars ℝ
  let W : H →ₗ[ℝ] State ((ℤ × Fin 2) × ι) →ₗ[ℝ] State ((ℤ × Fin 2) × ι) :=
    LinearMap.mk₂ ℝ (fun a u => S.symm (fun i => R (BR a (Z u i))))
      (by
        intro a b u
        simp only [map_add, add_apply, ← Pi.add_def])
      (by
        intro c a u
        simp only [map_smul, smul_apply, ← Pi.smul_def])
      (by
        intro a u v
        simp only [Z, map_add, Pi.add_apply, ← Pi.add_def])
      (by
        intro c a u
        simp only [Z, map_smul, Pi.smul_apply, ← Pi.smul_def])
  have hW (a : H) (u : State ((ℤ × Fin 2) × ι)) :
      ‖W a u‖ ≤ ((1 + (Fintype.card ι : ℝ)) * 4 * d) * ‖a‖ * ‖u‖ := by
    have hcomponent (i : ι) : ‖R (BR a (Z u i))‖ ≤ (4 * d) * ‖a‖ * ‖u‖ := by
      rw [R.norm_map]
      have hZ : ‖Z u i‖ ≤ ‖u‖ := by
        change ‖R.symm (S u i)‖ ≤ _
        rw [R.symm.norm_map]
        exact (norm_le_pi_norm (S u) i).trans (norm_lpFinitePiEquiv_le ℝ u)
      calc
        _ ≤ ‖B‖ * ‖a‖ * ‖Z u i‖ := B.le_opNorm₂ _ _
        _ ≤ (4 * d) * ‖a‖ * ‖u‖ := by gcongr
    have hp : ‖(fun i => R (BR a (Z u i)))‖ ≤ (4 * d) * ‖a‖ * ‖u‖ :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr hcomponent
    calc
      _ ≤ (1 + (Fintype.card ι : ℝ)) * ‖(fun i => R (BR a (Z u i)))‖ :=
        norm_lpFinitePiEquiv_symm_le ℝ _
      _ ≤ (1 + (Fintype.card ι : ℝ)) * ((4 * d) * ‖a‖ * ‖u‖) := by gcongr
      _ = _ := by ring
  let M := W.mkContinuous₂ ((1 + (Fintype.card ι : ℝ)) * 4 * d) hW
  have hM (a : H) (u : State ((ℤ × Fin 2) × ι)) (i : ι) :
      D (Z (M a u) i) = D a * D (Z u i) := by
    change D (R.symm (S (S.symm (fun i => R (BR a (Z u i)))) i)) = _
    rw [S.apply_symm_apply, R.symm_apply_apply]
    exact hB a (Z u i)
  refine ⟨M, hM, W.mkContinuous₂_norm_le (by positivity) hW, ?_⟩
  intro a ha u x i
  change (D (Z (M a u) i) x).re = (D a x).re * (D (Z u i) x).re
  rw [hM]
  change ((D a x) * (D (Z u i) x)).re = _
  rw [Complex.mul_re, ha x, zero_mul, sub_zero]

end PoincareConjecture.M63
