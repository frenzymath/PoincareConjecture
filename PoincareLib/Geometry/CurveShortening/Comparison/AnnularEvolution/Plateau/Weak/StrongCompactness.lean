import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.LocalizedCompactness
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Strong.Compactness

/-!
# Strong compactness of bounded weak maps on the annular rectangle

The weak derivative witness is the input. Localized compactness and the
uniform value bound produce global strong L2 compactness and a subsequence.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareMT

open Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain

/-- Bounded scalar weak annular maps with bounded columns have compact L2 closure. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
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

/-- Scalar weak annular bounds produce an actual strongly convergent L2 subsequence. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
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

end PoincareMT
