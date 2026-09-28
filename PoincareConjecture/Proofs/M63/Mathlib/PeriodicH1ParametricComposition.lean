import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1Composition
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1CoordinateContinuity
import PoincareConjecture.Proofs.M63.Mathlib.DenseParameterContinuity










set_option autoImplicit false

open AddCircle Set

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]





theorem exists_periodicH1_parametric_composition
    {P ι : Type*} [TopologicalSpace P] [Fintype ι]
    (Φ : P → (ι → ℂ) → ℂ) (Φ1 : P → (ι → ℂ) → (ι → ℂ) →L[ℝ] ℂ)
    (hΦcont : Continuous (fun z : P × (ι → ℂ) => Φ z.1 z.2))
    (hΦ1cont : Continuous (fun z : P × (ι → ℂ) => Φ1 z.1 z.2))
    (hΦ : ∀ p z, HasFDerivAt (Φ p) (Φ1 p z) z)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ p z, ‖Φ1 p z‖ ≤ A)
    (hLip : ∀ p z w, ‖Φ1 p z - Φ1 p w‖ ≤ B * ‖z - w‖) :
    ∃ G : P → (ι → lp (fun _ : ℤ => ℂ) 2) → lp (fun _ : ℤ => ℂ) 2,
      Continuous (fun z : P × (ι → lp (fun _ : ℤ => ℂ) 2) => G z.1 z.2) ∧
      (∀ p u x, periodicSobolevJet (L := L) 0 0 (by omega) (G p u) x =
        Φ p (periodicH1VectorDecoder (L := L) ι u x)) ∧
      ∀ p u v, ‖G p u - G p v‖ ≤ 4 * (1 + (Fintype.card ι : ℝ)) *
        (A * ‖u - v‖ + B * ‖periodicH1VectorDecoder (L := L) ι (u - v)‖ * ‖v‖) := by
  classical
  choose G _hG hdecode hest using fun p =>
    exists_periodicH1_composition (L := L) (Φ p) (Φ1 p) (hΦ p) hA hB (hbound p) (hLip p)
  refine ⟨G, ?_, hdecode, hest⟩
  let X := ι → lp (fun _ : ℤ => ℂ) 2
  let s : Set X := {u | ∀ i, u i ∈ periodicC1Core (L := L)}
  let D := periodicSobolevJet (L := L) 0 0 (by omega)
  let DX := periodicH1VectorDecoder (L := L) ι
  let c : ℝ := 4 * (1 + (Fintype.card ι : ℝ))
  let d := ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
    memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hd : 0 ≤ d := norm_nonneg _
  have hs : Dense s := by
    simpa only [Set.pi, Set.mem_univ, true_implies, SetLike.mem_coe, s, X] using
      dense_pi (univ : Set ι) (fun _ _ => dense_periodicC1Core (L := L))
  apply continuous_uncurry_of_dense_bounded_lipschitz G s hs
  · intro u hu
    let g (i : ι) : C(AddCircle L, ℂ) := (hu i).choose
    have hg (i : ι) (x : ℝ) : HasDerivAt
        (fun y : ℝ => D (u i) (y : AddCircle L)) (g i (x : AddCircle L)) x :=
      (hu i).choose_spec x
    let V : C(AddCircle L, ι → ℂ) :=
      ⟨fun x i => g i x, continuous_pi (fun i => (g i).continuous)⟩
    let C (p : P) : C(AddCircle L, ℂ) :=
      ⟨fun x => Φ p (DX u x), hΦcont.comp (continuous_const.prodMk (DX u).continuous)⟩
    let C1 (p : P) : C(AddCircle L, ℂ) :=
      ⟨fun x => Φ1 p (DX u x) (V x),
        (hΦ1cont.comp (continuous_const.prodMk (DX u).continuous)).clm_apply V.continuous⟩
    have hC : Continuous C := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact hΦcont.comp (continuous_fst.prodMk ((DX u).continuous.comp continuous_snd))
    have hC1 : Continuous C1 := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (hΦ1cont.comp (continuous_fst.prodMk ((DX u).continuous.comp continuous_snd))).clm_apply
        (V.continuous.comp continuous_snd)
    have hder (p : P) (x : ℝ) : HasDerivAt (fun y : ℝ => C p (y : AddCircle L))
        (C1 p (x : AddCircle L)) x := by
      have hv : HasDerivAt (fun y : ℝ => DX u (y : AddCircle L)) (V (x : AddCircle L)) x :=
        hasDerivAt_pi.mpr (fun i => hg i x)
      exact (hΦ p (DX u (x : AddCircle L))).comp_hasDerivAt x hv
    have heq (p : P) : G p u = periodicH1Coordinates (C p) (C1 p) (hder p) := by
      apply periodicH1Decoder_injective (L := L)
      rw [periodicH1Coordinates_reconstruct]
      ext x
      exact hdecode p u x
    simpa only [heq] using continuous_periodicH1Coordinates C C1 hC hC1 hder
  · intro R hR
    refine ⟨⟨c * (A + B * d * R), by positivity⟩, ?_⟩
    intro p
    apply LipschitzOnWith.of_dist_le_mul
    intro u _ v hv
    simp only [dist_eq_norm]
    have hDX : ‖DX (u - v)‖ ≤ d * ‖u - v‖ := norm_periodicH1VectorDecoder_le _
    calc
      ‖G p u - G p v‖ ≤ c * (A * ‖u - v‖ + B * ‖DX (u - v)‖ * ‖v‖) := hest p u v
      _ ≤ c * (A * ‖u - v‖ + B * (d * ‖u - v‖) * R) := by
        gcongr
        exact hv
      _ = (c * (A + B * d * R)) * ‖u - v‖ := by ring

end PoincareConjecture.M63
