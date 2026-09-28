import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakLocalizedCompactness
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.StrongCompactness

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain

theorem m64Annulus_weak_l2_isCompact
    (u : ℕ → LoopPlane → ℝ) (hw : ∀ j, MemW1pWitness 2 (u j) S)
    {A C : ℝ} (hA : ∀ j p, ‖u j p‖ ≤ A)
    (hC : ∀ j (i : Fin 2), (∫ p in S, ((hw j).weakGrad p i) ^ 2) ≤ C) :
    ∃ hU : ∀ j, MemLp ((S).indicator (u j)) 2 volume,
      IsCompact (closure (range (fun j => (hU j).toLp ((S).indicator (u j))))) := by
  have hfinite : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top m64AnnulusDomain_volume_ne_top (measure_mono interior_subset)
  have hA0 : 0 ≤ A := (norm_nonneg (u 0 0)).trans (hA 0 0)
  have hv (j : ℕ) : (∫ p in S, u j p ^ 2) ≤ volume.real S * A ^ 2 := by
    calc
      _ ≤ ∫ _p in S, A ^ 2 := by
        apply integral_mono (hw j).memLp.integrable_sq (integrableOn_const hfinite)
        intro p
        simpa only [Real.norm_eq_abs, sq_abs] using
          (sq_le_sq₀ (norm_nonneg _) hA0).mpr (hA j p)
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  apply m64Annulus_l2_isCompact_of_localized u (fun j => (hw j).memLp) hA
  intro phi hphi hc hs
  exact m64WeakSobolev_localized_l2_isCompact isOpen_interior u hw hv hC phi hphi hc hs

theorem m64Annulus_weak_strong_subsequence
    (u : ℕ → LoopPlane → ℝ) (hw : ∀ j, MemW1pWitness 2 (u j) S)
    {A C : ℝ} (hA : ∀ j p, ‖u j p‖ ≤ A)
    (hC : ∀ j (i : Fin 2), (∫ p in S, ((hw j).weakGrad p i) ^ 2) ≤ C) :
    ∃ (hU : ∀ j, MemLp ((S).indicator (u j)) 2 volume)
      (v : Lp ℝ 2 (volume : Measure LoopPlane)) (k : ℕ → ℕ),
      StrictMono k ∧ Tendsto (fun j => (hU (k j)).toLp ((S).indicator (u (k j))))
        atTop (𝓝 v) := by
  obtain ⟨hU, hc⟩ := m64Annulus_weak_l2_isCompact u hw hA hC
  obtain ⟨v, -, k, hk, hv⟩ := hc.isSeqCompact (fun j => subset_closure (mem_range_self j))
  exact ⟨hU, v, k, hk, hv⟩

end PoincareConjecture
