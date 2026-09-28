import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorPeriodicH1Coefficients
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1ParametricComposition

set_option autoImplicit false

open PoincareConjecture.SpectralHeatNative

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)] {P ι : Type*} [TopologicalSpace P] [Fintype ι]

theorem exists_realScalarH1_composition
    (f : P → ((Fin 2 × ι) → ℝ) → ℝ)
    (f1 : P → ((Fin 2 × ι) → ℝ) → ((Fin 2 × ι) → ℝ) →L[ℝ] ℝ)
    (hfcont : Continuous (fun z : P × ((Fin 2 × ι) → ℝ) => f z.1 z.2))
    (hf1cont : Continuous (fun z : P × ((Fin 2 × ι) → ℝ) => f1 z.1 z.2))
    (hf : ∀ p z, HasFDerivAt (f p) (f1 p z) z)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ p z, ‖f1 p z‖ ≤ A)
    (hLip : ∀ p z w, ‖f1 p z - f1 p w‖ ≤ B * ‖z - w‖) :
    ∃ G : P → State ((ℤ × Fin 2) × ι) → lp (fun _ : ℤ => ℂ) 2,
      Continuous (fun z : P × State ((ℤ × Fin 2) × ι) => G z.1 z.2) ∧
      (∀ p u x, periodicSobolevJet (L := L) 0 0 (by omega) (G p u) x =
        (f p (fun j : Fin 2 × ι => vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) : ℂ)) ∧
      ∀ p u v, ‖G p u - G p v‖ ≤ 4 * (1 + (Fintype.card (Fin 2 × ι) : ℝ)) *
        (A + B * ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
          memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖ * ‖v‖) *
          ‖u - v‖ := by
  let J := Fin 2 × ι
  let R : (J → ℂ) →L[ℝ] (J → ℝ) :=
    ContinuousLinearMap.pi (fun j => Complex.reCLM.comp (ContinuousLinearMap.proj j))
  have hR (z : J → ℂ) : ‖R z‖ ≤ ‖z‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro j
    exact (Complex.abs_re_le_norm (z j)).trans (norm_le_pi_norm z j)
  let Φ (p : P) (z : J → ℂ) : ℂ := f p (R z)
  let Φ1 (p : P) (z : J → ℂ) : (J → ℂ) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp ((f1 p (R z)).comp R)
  have hΦcont : Continuous (fun z : P × (J → ℂ) => Φ z.1 z.2) :=
    Complex.ofRealCLM.continuous.comp
      (hfcont.comp (continuous_fst.prodMk (R.continuous.comp continuous_snd)))
  have hΦ1cont : Continuous (fun z : P × (J → ℂ) => Φ1 z.1 z.2) :=
    continuous_const.clm_comp
      ((hf1cont.comp (continuous_fst.prodMk (R.continuous.comp continuous_snd))).clm_comp
        continuous_const)
  have hΦ (p : P) (z : J → ℂ) : HasFDerivAt (Φ p) (Φ1 p z) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z ((hf p (R z)).comp z R.hasFDerivAt)
  have hΦbound (p : P) (z : J → ℂ) : ‖Φ1 p z‖ ≤ A := by
    apply ContinuousLinearMap.opNorm_le_bound _ hA
    intro v
    change ‖(f1 p (R z) (R v) : ℂ)‖ ≤ _
    rw [Complex.norm_real]
    exact ((f1 p (R z)).le_opNorm (R v)).trans
      (mul_le_mul (hbound p (R z)) (hR v) (norm_nonneg _) hA)
  have hΦLip (p : P) (z w : J → ℂ) : ‖Φ1 p z - Φ1 p w‖ ≤ B * ‖z - w‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change ‖(f1 p (R z) (R v) : ℂ) - (f1 p (R w) (R v) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub, Complex.norm_real]
    change ‖(f1 p (R z) - f1 p (R w)) (R v)‖ ≤ _
    calc
      _ ≤ ‖f1 p (R z) - f1 p (R w)‖ * ‖R v‖ :=
        (f1 p (R z) - f1 p (R w)).le_opNorm _
      _ ≤ (B * ‖R (z - w)‖) * ‖R v‖ := by rw [map_sub]; gcongr; exact hLip p (R z) (R w)
      _ ≤ (B * ‖z - w‖) * ‖v‖ := by
        gcongr
        · exact hR (z - w)
        · exact hR v
  obtain ⟨G, hGcont, hGdecode, hGest⟩ :=
    exists_periodicH1_parametric_composition (L := L) Φ Φ1 hΦcont hΦ1cont hΦ hA hB hΦbound hΦLip
  let X := vectorPeriodicH1JetCoordinates (L := L) (ι := ι)
  let d := ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
    memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖
  refine ⟨fun p u => G p (X u),
    hGcont.comp (continuous_fst.prodMk (X.continuous.comp continuous_snd)), ?_, ?_⟩
  · intro p u x
    rw [hGdecode]
    change (f p (R (periodicH1VectorDecoder (L := L) J (X u) x)) : ℂ) = _
    apply congrArg (fun z : J → ℝ => (f p z : ℂ))
    funext j
    exact (vectorPeriodicH1JetCoordinates_spec (L := L) u).2.2 j x
  · intro p u v
    have hXδ : ‖X u - X v‖ ≤ ‖u - v‖ := by
      rw [← map_sub]
      exact (vectorPeriodicH1JetCoordinates_spec (L := L) (u - v)).1
    have hXv : ‖X v‖ ≤ ‖v‖ := (vectorPeriodicH1JetCoordinates_spec (L := L) v).1
    have hDX : ‖periodicH1VectorDecoder (L := L) J (X u - X v)‖ ≤ d * ‖u - v‖ :=
      (norm_periodicH1VectorDecoder_le _).trans
        (mul_le_mul_of_nonneg_left hXδ (norm_nonneg _))
    calc
      _ ≤ 4 * (1 + (Fintype.card J : ℝ)) *
          (A * ‖X u - X v‖ + B * ‖periodicH1VectorDecoder (L := L) J (X u - X v)‖ * ‖X v‖) :=
        hGest p (X u) (X v)
      _ ≤ 4 * (1 + (Fintype.card J : ℝ)) *
          (A * ‖u - v‖ + B * (d * ‖u - v‖) * ‖v‖) := by gcongr
      _ = _ := by ring

theorem exists_realVectorH1_composition
    (f : P → ((Fin 2 × ι) → ℝ) → (ι → ℝ))
    (f1 : P → ((Fin 2 × ι) → ℝ) → ((Fin 2 × ι) → ℝ) →L[ℝ] (ι → ℝ))
    (hfcont : Continuous (fun z : P × ((Fin 2 × ι) → ℝ) => f z.1 z.2))
    (hf1cont : Continuous (fun z : P × ((Fin 2 × ι) → ℝ) => f1 z.1 z.2))
    (hf : ∀ p z, HasFDerivAt (f p) (f1 p z) z)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ p z, ‖f1 p z‖ ≤ A)
    (hLip : ∀ p z w, ‖f1 p z - f1 p w‖ ≤ B * ‖z - w‖) :
    ∃ G : P → State ((ℤ × Fin 2) × ι) → State ((ℤ × Fin 2) × ι),
      Continuous (fun z : P × State ((ℤ × Fin 2) × ι) => G z.1 z.2) ∧
      (∀ p u x i, periodicSobolevJet (L := L) 0 0 (by omega)
          (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (G p u) i)) x =
        (f p (fun j : Fin 2 × ι => vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) i : ℂ)) ∧
      ∀ p u v, ‖G p u - G p v‖ ≤
        (1 + (Fintype.card ι : ℝ)) * (4 * (1 + (Fintype.card (Fin 2 × ι) : ℝ))) *
        (A + B * ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
          memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖ * ‖v‖) *
          ‖u - v‖ := by
  classical
  let c : ℝ := 4 * (1 + (Fintype.card (Fin 2 × ι) : ℝ))
  let d := ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
    memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖
  have hcomponent (i : ι) :
      ∃ G : P → State ((ℤ × Fin 2) × ι) → lp (fun _ : ℤ => ℂ) 2,
        Continuous (fun z : P × State ((ℤ × Fin 2) × ι) => G z.1 z.2) ∧
        (∀ p u x, periodicSobolevJet (L := L) 0 0 (by omega) (G p u) x =
          (f p (fun j : Fin 2 × ι => vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) i : ℂ)) ∧
        ∀ p u v, ‖G p u - G p v‖ ≤ c * (A + B * d * ‖v‖) * ‖u - v‖ := by
    let E : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    apply exists_realScalarH1_composition (L := L) (fun p z => E (f p z))
      (fun p z => E.comp (f1 p z))
      (E.continuous.comp hfcont) (continuous_const.clm_comp hf1cont)
      (fun p z => E.hasFDerivAt.comp z (hf p z)) hA hB
    · intro p z
      apply ContinuousLinearMap.opNorm_le_bound _ hA
      intro v
      exact (norm_le_pi_norm (f1 p z v) i).trans
        (((f1 p z).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hbound p z) (norm_nonneg v)))
    · intro p z w
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      change ‖((f1 p z - f1 p w) v) i‖ ≤ _
      exact (norm_le_pi_norm ((f1 p z - f1 p w) v) i).trans
        (((f1 p z - f1 p w).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hLip p z w) (norm_nonneg v)))
  choose G hGcont hGdecode hGest using hcomponent
  let S := lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ
  let R := complexLpRealEquiv (ι := ℤ)
  refine ⟨fun p u => S.symm (fun i => R (G i p u)), ?_, ?_, ?_⟩
  · exact S.symm.continuous.comp (continuous_pi (fun i => R.continuous.comp (hGcont i)))
  · intro p u x i
    change periodicSobolevJet (L := L) 0 0 (by omega)
      (R.symm (S (S.symm (fun i => R (G i p u))) i)) x = _
    rw [S.apply_symm_apply, R.symm_apply_apply]
    exact hGdecode i p u x
  · intro p u v
    rw [← map_sub]
    have hpi : ‖(fun i => R (G i p u)) - (fun i => R (G i p v))‖ ≤
        c * (A + B * d * ‖v‖) * ‖u - v‖ := by
      apply (pi_norm_le_iff_of_nonneg (by dsimp [c, d]; positivity)).mpr
      intro i
      simpa only [Pi.sub_apply, ← map_sub, R.norm_map] using hGest i p u v
    calc
      _ ≤ (1 + (Fintype.card ι : ℝ)) *
          ‖(fun i => R (G i p u)) - (fun i => R (G i p v))‖ :=
        norm_lpFinitePiEquiv_symm_le ℝ _
      _ ≤ (1 + (Fintype.card ι : ℝ)) * (c * (A + B * d * ‖v‖) * ‖u - v‖) := by gcongr
      _ = _ := by ring

end PoincareConjecture.M63
