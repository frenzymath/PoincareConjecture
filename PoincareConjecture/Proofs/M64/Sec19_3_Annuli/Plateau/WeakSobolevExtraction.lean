import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakVectorCompactness
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.HilbertExtraction
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64Annulus_weak_sobolev_subsequence
    (u : ℕ → LoopPlane → E) (V : ℕ → Fin 2 → LoopPlane → E)
    (hu : ∀ j, MemLp (u j) 2 mu) (hV : ∀ j i, MemLp (V j i) 2 mu)
    (hweak : ∀ j i b, HasWeakPartialDeriv i (fun p => V j i p b) (fun p => u j p b) S)
    {A C : ℝ} (hA : ∀ j p, ‖u j p‖ ≤ A)
    (hC : ∀ j i, (∫ p in S, ‖V j i p‖ ^ 2) ≤ C) :
    ∃ (k : ℕ → ℕ) (U : Lp E 2 mu) (W : Fin 2 → Lp E 2 mu),
      StrictMono k ∧ Tendsto (fun j => (hu (k j)).toLp (u (k j))) atTop (𝓝 U) ∧
      (∀ i, WeakConverges (fun j => (hV (k j) i).toLp (V (k j) i)) (W i)) ∧
      ∀ᵐ p ∂mu, Tendsto (fun j => u (k j) p) atTop (𝓝 (U p)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨hU, hc⟩ := m64Annulus_weak_vector_l2_isCompact u V hu hV hweak hA hC
  obtain ⟨z, -, k0, hk0, hz⟩ := hc.isSeqCompact
    (fun j => subset_closure (mem_range_self j))
  have hmu : mu ≤ (1 : ℝ≥0∞) • volume := by
    simpa only [one_smul] using (Measure.restrict_le_self : mu ≤ volume)
  let R : Lp E 2 (volume : Measure LoopPlane) →L[ℝ] Lp E 2 mu :=
    Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hmu
  have hRmap (j : ℕ) : R ((hU j).toLp ((S).indicator (u j))) = (hu j).toLp (u j) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hmu
      ((hU j).toLp ((S).indicator (u j))), ae_restrict_of_ae (hU j).coeFn_toLp,
      (hu j).coeFn_toLp, ae_restrict_mem isOpen_interior.measurableSet] with p hp hp0 hp1 hpS
    rw [hp, hp0, hp1]
    exact indicator_of_mem hpS _
  have hstrong : Tendsto (fun j => (hu (k0 j)).toLp (u (k0 j))) atTop (𝓝 (R z)) := by
    exact ((R.continuous.tendsto z).comp hz).congr' (Eventually.of_forall fun j => hRmap (k0 j))
  have hnorm (j : ℕ) (i : Fin 2) :
      ‖(hV j i).toLp (V j i)‖ ≤ Real.sqrt (max C 0) := by
    apply Real.le_sqrt_of_sq_le
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    calc
      _ = ∫ p in S, ‖V j i p‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [(hV j i).coeFn_toLp] with p hp
        rw [hp]
      _ ≤ C := hC j i
      _ ≤ max C 0 := le_max_left _ _
  obtain ⟨w0, k1, hk1, hw0⟩ := m64SeparableHilbert_weak_subsequence
    (fun j => (hV (k0 j) 0).toLp (V (k0 j) 0)) (fun j => hnorm (k0 j) 0)
  obtain ⟨w1, k2, hk2, hw1⟩ := m64SeparableHilbert_weak_subsequence
    (fun j => (hV (k0 (k1 j)) 1).toLp (V (k0 (k1 j)) 1))
      (fun j => hnorm (k0 (k1 j)) 1)
  have hstrong2 := (hstrong.comp hk1.tendsto_atTop).comp hk2.tendsto_atTop
  obtain ⟨k3, hk3, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hstrong2).exists_seq_tendsto_ae
  let k := k0 ∘ k1 ∘ k2 ∘ k3
  let W : Fin 2 → Lp E 2 mu := ![w0, w1]
  refine ⟨k, R z, W, hk0.comp (hk1.comp (hk2.comp hk3)),
    hstrong2.comp hk3.tendsto_atTop, ?_, ?_⟩
  · intro i
    fin_cases i
    · intro L
      exact ((hw0 L).comp hk2.tendsto_atTop).comp hk3.tendsto_atTop
    · intro L
      exact (hw1 L).comp hk3.tendsto_atTop
  · have hcoe : ∀ᵐ p ∂mu, ∀ j, ((hu (k j)).toLp (u (k j))) p = u (k j) p :=
      ae_all_iff.mpr (fun j => (hu (k j)).coeFn_toLp)
    filter_upwards [hae, hcoe] with p hp hrep
    exact hp.congr' (Eventually.of_forall hrep)

end PoincareConjecture
