import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorSpectralTranslation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorPeriodicH1Coefficients
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicFourierCoordinates

set_option autoImplicit false

open Set PoincareConjecture.SpectralHeatNative

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]

local notation "S" => State ((ℤ × Fin 2) × ι)
local notation "H" => lp (fun _ : ℤ => ℂ) 2

theorem vectorPeriodicH1_product_spectralTranslation
    (M : H →L[ℝ] S →L[ℝ] S)
    (hM : ∀ c u i, periodicSobolevJet (L := L) 0 0 (by omega)
        (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (M c u) i)) =
      periodicSobolevJet (L := L) 0 0 (by omega) c *
        periodicSobolevJet (L := L) 0 0 (by omega)
          (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ u i)))
    (s : ℝ) (c : H) (u : S) :
    vectorPeriodicSpectralTranslation (L := L) s (M c u) =
      M (periodicSpectralTranslation (L := L) s c)
        (vectorPeriodicSpectralTranslation (L := L) s u) := by
  apply (lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ).injective
  funext i
  apply complexLpRealEquiv.symm.injective
  apply periodicH1Decoder_injective (L := L)
  rw [(vectorPeriodicSpectralTranslation_spec s (M c u)).1 i,
    (realPeriodicSpectralTranslation_spec s _).1,
    periodicSobolevJet_periodicSpectralTranslation, hM, hM,
    periodicSobolevJet_periodicSpectralTranslation,
    (vectorPeriodicSpectralTranslation_spec s u).1 i,
    (realPeriodicSpectralTranslation_spec s _).1,
    periodicSobolevJet_periodicSpectralTranslation]
  rfl

theorem local_periodicH1_coefficients_spectralTranslation
    (G : ℝ × S → H) (Q : ℝ × S → S)
    (g : ℝ → ((Fin 2 × ι) → ℝ) → ℝ)
    (q : ℝ → ((Fin 2 × ι) → ℝ) → ι → ℝ)
    {O : Set (ℝ × S)}
    (hdecode : ∀ t u, 0 ≤ t → (t, u) ∈ O → ∀ x : AddCircle L,
      periodicSobolevJet (L := L) 0 0 (by omega) (G (t, u)) x =
        (g t (fun j => vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) : ℂ) ∧
      ∀ i, periodicSobolevJet (L := L) 0 0 (by omega)
          (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (Q (t, u)) i)) x =
        (q t (fun j => vectorPeriodicJet (L := L) 1 j.1 (by omega) u x j.2) i : ℂ))
    (s : ℝ) {t : ℝ} {u : S} (ht : 0 ≤ t) (hu : (t, u) ∈ O)
    (hsu : (t, vectorPeriodicSpectralTranslation (L := L) s u) ∈ O) :
    G (t, vectorPeriodicSpectralTranslation (L := L) s u) =
        periodicSpectralTranslation (L := L) s (G (t, u)) ∧
      Q (t, vectorPeriodicSpectralTranslation (L := L) s u) =
        vectorPeriodicSpectralTranslation (L := L) s (Q (t, u)) := by
  have hjet (x : AddCircle L) :
      (fun j : Fin 2 × ι => vectorPeriodicJet (L := L) 1 j.1 (by omega)
        (vectorPeriodicSpectralTranslation (L := L) s u) x j.2) =
      fun j : Fin 2 × ι => vectorPeriodicJet (L := L) 1 j.1 (by omega)
        u (x - (s : AddCircle L)) j.2 := by
    funext j
    rw [vectorPeriodicJet_spectralTranslation]
    rfl
  constructor
  · apply periodicH1Decoder_injective (L := L)
    rw [periodicSobolevJet_periodicSpectralTranslation]
    apply ContinuousMap.ext
    intro x
    change periodicSobolevJet (L := L) 0 0 (by omega)
      (G (t, vectorPeriodicSpectralTranslation (L := L) s u)) x =
        periodicSobolevJet (L := L) 0 0 (by omega)
          (G (t, u)) (x - (s : AddCircle L))
    rw [(hdecode t _ ht hsu x).1, (hdecode t u ht hu _).1, hjet]
  · apply (lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ).injective
    funext i
    apply complexLpRealEquiv.symm.injective
    apply periodicH1Decoder_injective (L := L)
    rw [(vectorPeriodicSpectralTranslation_spec s (Q (t, u))).1 i,
      (realPeriodicSpectralTranslation_spec s _).1,
      periodicSobolevJet_periodicSpectralTranslation]
    apply ContinuousMap.ext
    intro x
    change periodicSobolevJet (L := L) 0 0 (by omega)
      (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ
        (Q (t, vectorPeriodicSpectralTranslation (L := L) s u)) i)) x =
      periodicSobolevJet (L := L) 0 0 (by omega)
        (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (Q (t, u)) i))
          (x - (s : AddCircle L))
    rw [(hdecode t _ ht hsu x).2 i, (hdecode t u ht hu _).2 i, hjet]

end PoincareConjecture.M63
