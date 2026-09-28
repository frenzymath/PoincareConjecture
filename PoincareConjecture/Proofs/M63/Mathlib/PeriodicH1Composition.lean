import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1CompositionCore
import PoincareConjecture.Proofs.M63.Mathlib.DenseNonlinearExtension

set_option autoImplicit false

open AddCircle Set

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

theorem exists_periodicH1_composition {ι : Type*} [Fintype ι]
    (Φ : (ι → ℂ) → ℂ) (Φ1 : (ι → ℂ) → (ι → ℂ) →L[ℝ] ℂ)
    (hΦ : ∀ z, HasFDerivAt Φ (Φ1 z) z) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ z, ‖Φ1 z‖ ≤ A)
    (hLip : ∀ z w, ‖Φ1 z - Φ1 w‖ ≤ B * ‖z - w‖) :
    ∃ F : (ι → lp (fun _ : ℤ => ℂ) 2) → lp (fun _ : ℤ => ℂ) 2,
      Continuous F ∧
      (∀ u x, periodicSobolevJet (L := L) 0 0 (by omega) (F u) x =
        Φ (periodicH1VectorDecoder (L := L) ι u x)) ∧
      ∀ u v, ‖F u - F v‖ ≤ 4 * (1 + (Fintype.card ι : ℝ)) *
        (A * ‖u - v‖ + B * ‖periodicH1VectorDecoder (L := L) ι (u - v)‖ * ‖v‖) := by
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
  obtain ⟨f, hdecode, hest⟩ := exists_periodicH1_core_composition (L := L)
    Φ Φ1 hΦ hA hB hbound hLip
  have hf : ∀ R : ℝ, 0 < R → ∃ K : NNReal,
      LipschitzOnWith K f {u : s | ‖(u : X)‖ ≤ R} := by
    intro R hR
    refine ⟨⟨c * (A + B * d * R), by positivity⟩, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro u _ v hv
    simp only [Subtype.dist_eq, dist_eq_norm]
    have hDX : ‖DX (u.val - v.val)‖ ≤ d * ‖u.val - v.val‖ :=
      norm_periodicH1VectorDecoder_le _
    calc
      ‖f u - f v‖ ≤ c * (A * ‖u.val - v.val‖ + B * ‖DX (u.val - v.val)‖ * ‖v.val‖) := hest u v
      _ ≤ c * (A * ‖u.val - v.val‖ + B * (d * ‖u.val - v.val‖) * R) := by
        gcongr
        exact hv
      _ = (c * (A + B * d * R)) * ‖u.val - v.val‖ := by ring
  obtain ⟨F, hF, hcore⟩ := exists_continuous_extension_of_bounded_lipschitz s hs f hf
  have hΦcont : Continuous Φ := continuous_iff_continuousAt.mpr (fun z => (hΦ z).continuousAt)
  have hsd : DenseRange (Subtype.val : s → X) := hs.denseRange_val
  refine ⟨F, hF, ?_, ?_⟩
  · intro u x
    refine hsd.induction_on u ?_ ?_
    · exact isClosed_eq
        ((ContinuousMap.evalCLM ℂ x).continuous.comp (D.continuous.comp hF))
        (hΦcont.comp ((ContinuousMap.evalCLM ℂ x).continuous.comp DX.continuous))
    · intro v
      rw [hcore]
      exact hdecode v x
  · intro u v
    refine hsd.induction_on₂ (p := fun a b => ‖F a - F b‖ ≤
      c * (A * ‖a - b‖ + B * ‖DX (a - b)‖ * ‖b‖)) ?_ ?_ u v
    · apply isClosed_le
      · exact ((hF.comp continuous_fst).sub (hF.comp continuous_snd)).norm
      · fun_prop
    · intro a b
      rw [hcore, hcore]
      exact hest a b

end PoincareConjecture.M63
