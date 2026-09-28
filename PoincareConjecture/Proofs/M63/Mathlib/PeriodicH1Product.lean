import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1Core
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1ProductEnergy
import PoincareConjecture.Proofs.M63.Mathlib.DenseBilinearExtension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option autoImplicit false

set_option maxSynthPendingDepth 3

open AddCircle Set

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

theorem exists_periodicH1_core_product :
    ∃ B : periodicC1Core (L := L) →L[ℂ]
        periodicC1Core (L := L) →L[ℂ] lp (fun _ : ℤ => ℂ) 2,
      (∀ u v, periodicSobolevJet (L := L) 0 0 (by omega) (B u v) =
        periodicSobolevJet (L := L) 0 0 (by omega) u *
          periodicSobolevJet (L := L) 0 0 (by omega) v) ∧
      ‖B‖ ≤ 4 * ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
        memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖ := by
  classical
  let H := lp (fun _ : ℤ => ℂ) 2
  let S := periodicC1Core (L := L)
  let D := periodicSobolevJet (L := L) 0 0 (by omega)
  let d := ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
    memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖
  have hD : Function.Injective D := periodicH1Decoder_injective
  have hu (u : S) : ∃ g : C(AddCircle L, ℂ), ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => D u (y : AddCircle L)) (g (x : AddCircle L)) x := u.property
  choose g hg using hu
  have hE (u : S) : periodicH1Coordinates (D u) (g u) (hg u) = (u : H) :=
    hD (periodicH1Coordinates_reconstruct (D u) (g u) (hg u))
  have hprod (u v : S) : ∃ w : H, D w = D u * D v ∧
      ‖w‖ ≤ 2 * (‖D u‖ * ‖(v : H)‖ + ‖D v‖ * ‖(u : H)‖) := by
    obtain ⟨hfg, hbound⟩ := periodicH1Coordinates_product_bound (D u) (g u) (D v) (g v)
      (hg u) (hg v)
    refine ⟨periodicH1Coordinates (D u * D v) (g u * D v + D u * g v) hfg,
      periodicH1Coordinates_reconstruct _ _ hfg, ?_⟩
    simpa only [hE] using hbound
  choose W hW hWnorm using hprod
  let B₀ : S →ₗ[ℂ] S →ₗ[ℂ] H := LinearMap.mk₂ ℂ W
    (by
      intro u v w
      apply hD
      rw [hW, map_add, hW, hW]
      change D ((u : H) + (v : H)) * D w = _
      rw [map_add, add_mul])
    (by
      intro c u v
      apply hD
      rw [hW, map_smul, hW]
      change D (c • (u : H)) * D v = _
      rw [map_smul, smul_mul_assoc])
    (by
      intro u v w
      apply hD
      rw [hW, map_add, hW, hW]
      change D u * D ((v : H) + (w : H)) = _
      rw [map_add, mul_add])
    (by
      intro c u v
      apply hD
      rw [hW, map_smul, hW]
      change D u * D (c • (v : H)) = _
      rw [map_smul, mul_smul_comm])
  have hB (u v : S) : ‖B₀ u v‖ ≤ (4 * d) * ‖u‖ * ‖v‖ := by
    have hDu : ‖D u‖ ≤ d * ‖(u : H)‖ := norm_periodicSobolevJet_le 0 0 (by omega) u
    have hDv : ‖D v‖ ≤ d * ‖(v : H)‖ := norm_periodicSobolevJet_le 0 0 (by omega) v
    calc
      ‖B₀ u v‖ ≤ 2 * (‖D u‖ * ‖(v : H)‖ + ‖D v‖ * ‖(u : H)‖) := hWnorm u v
      _ ≤ 2 * ((d * ‖(u : H)‖) * ‖(v : H)‖ + (d * ‖(v : H)‖) * ‖(u : H)‖) := by
        gcongr
      _ = (4 * d) * ‖u‖ * ‖v‖ := by change _ = (4 * d) * ‖(u : H)‖ * ‖(v : H)‖; ring
  refine ⟨B₀.mkContinuous₂ (4 * d) hB, ?_, ?_⟩
  · exact hW
  · exact B₀.mkContinuous₂_norm_le (by positivity) hB

theorem exists_periodicH1_product :
    ∃ B : lp (fun _ : ℤ => ℂ) 2 →L[ℂ]
        lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2,
      (∀ u v, periodicSobolevJet (L := L) 0 0 (by omega) (B u v) =
        periodicSobolevJet (L := L) 0 0 (by omega) u *
          periodicSobolevJet (L := L) 0 0 (by omega) v) ∧
      ‖B‖ ≤ 4 * ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
        memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖ := by
  obtain ⟨Bcore, hcore, hnorm⟩ := exists_periodicH1_core_product (L := L)
  obtain ⟨B, hext, hBnorm⟩ := exists_dense_bilinear_extension
    (periodicC1Core (L := L)) (periodicC1Core (L := L))
    dense_periodicC1Core dense_periodicC1Core Bcore
  refine ⟨B, ?_, hBnorm.trans hnorm⟩
  let D := periodicSobolevJet (L := L) 0 0 (by omega)
  have hd : DenseRange (periodicC1Core (L := L)).subtypeL :=
    dense_periodicC1Core.denseRange_val
  intro u v
  refine hd.induction_on₂ (p := fun a b => D (B a b) = D a * D b) ?_ ?_ u v
  · exact isClosed_eq (D.continuous.comp B.continuous₂)
      ((D.continuous.comp continuous_fst).mul (D.continuous.comp continuous_snd))
  · intro a b
    change D (B (a : lp (fun _ : ℤ => ℂ) 2) (b : lp (fun _ : ℤ => ℂ) 2)) = _
    rw [hext]
    exact hcore a b

end PoincareConjecture.M63
