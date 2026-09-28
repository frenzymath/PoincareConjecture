import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.RealPeriodicJets
import PoincareConjecture.Proofs.M63.Mathlib.FiniteLpCoordinates
import Mathlib.Analysis.Calculus.Deriv.Prod









set_option autoImplicit false

open PoincareConjecture.SpectralHeatNative

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]




noncomputable def vectorPeriodicJet (k j : ℕ) (hj : j ≤ k) :
    State ((ℤ × Fin 2) × ι) →L[ℝ] C(AddCircle L, ι → ℝ) := by
  let D := realPeriodicJet (L := L) k j hj
  let S := lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ
  let A : State ((ℤ × Fin 2) × ι) →ₗ[ℝ] C(AddCircle L, ι → ℝ) :=
    { toFun := fun u => ⟨fun x i => D (S u i) x,
        continuous_pi (fun i => (D (S u i)).continuous)⟩
      map_add' := by
        intro u v
        ext x i
        change D (S (u + v) i) x = (D (S u i) + D (S v i)) x
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro c u
        ext x i
        change D (S (c • u) i) x = (c • D (S u i)) x
        simp only [map_smul, Pi.smul_apply] }
  let d := ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
    memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖
  apply A.mkContinuous d
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  change ‖D (S u i) x‖ ≤ d * ‖u‖
  exact ((D (S u i)).norm_coe_le_norm x).trans
    ((norm_realPeriodicJet_le k j hj (S u i)).trans
      (mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm (S u) i).trans (norm_lpFinitePiEquiv_le ℝ u)) (norm_nonneg _)))




theorem norm_vectorPeriodicJet_le (k j : ℕ) (hj : j ≤ k) (u : State ((ℤ × Fin 2) × ι)) :
    ‖vectorPeriodicJet (L := L) k j hj u‖ ≤
      ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
        memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖ * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  change ‖realPeriodicJet (L := L) k j hj (lpFinitePiEquiv ℝ u i) x‖ ≤ _
  exact ((realPeriodicJet (L := L) k j hj (lpFinitePiEquiv ℝ u i)).norm_coe_le_norm x).trans
    ((norm_realPeriodicJet_le k j hj (lpFinitePiEquiv ℝ u i)).trans
      (mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm (lpFinitePiEquiv ℝ u) i).trans (norm_lpFinitePiEquiv_le ℝ u))
        (norm_nonneg _)))




theorem hasDerivAt_vectorPeriodicJet {k j : ℕ} (hj : j < k)
    (u : State ((ℤ × Fin 2) × ι)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => vectorPeriodicJet (L := L) k j hj.le u (y : AddCircle L))
      (vectorPeriodicJet (L := L) k (j + 1) hj u (x : AddCircle L)) x := by
  apply hasDerivAt_pi.mpr
  intro i
  exact hasDerivAt_realPeriodicJet hj (lpFinitePiEquiv ℝ u i) x




theorem vectorPeriodicJet_scaleDecode (k j l : ℕ) (hj : j ≤ k)
    (u : State ((ℤ × Fin 2) × ι)) :
    vectorPeriodicJet (L := L) k j hj
      (scaleDecode (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) l u) =
      vectorPeriodicJet (L := L) (k + l) j (hj.trans (Nat.le_add_right k l)) u := by
  have hsplit (i : ι) :
      lpFinitePiEquiv ℝ
          (scaleDecode (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) l u) i =
        scaleDecode (periodicSpectrum L) l (lpFinitePiEquiv ℝ u i) := by
    apply lp.ext
    funext p
    rfl
  ext x i
  change realPeriodicJet (L := L) k j hj
    (lpFinitePiEquiv ℝ
      (scaleDecode (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) l u) i) x = _
  rw [hsplit, realPeriodicJet_scaleDecode]
  rfl

end PoincareConjecture.M63
