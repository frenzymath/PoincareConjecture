import PoincareLib.Analysis.Sobolev.Euclidean.FrechetKolmogorov
import PoincareLib.Analysis.Sobolev.Euclidean.L2

/-!
# Compactness for smooth Euclidean functions with bounded first derivatives

The smooth Rellich theorem follows from the translation estimate and the
Frechet--Kolmogorov argument adapted from Chow--Liao--Qin, revision
`1b535dd102b94cc42b107cca27059687888f08b3`.
The upstream source is licensed under Apache-2.0; see
`references/ricci-flow/chow-liao-qin-2026/LICENSE.Apache-2.0.txt`.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal

namespace Poincare.Analysis.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Uniform bounds on the first derivatives give uniform translation control. -/
theorem uniform_translation_of_eLpNorm_fderiv_le
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : ℕ → E → ℝ}
    (hu_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n))
    {S : ℝ}
    (hu_deriv : ∀ n,
      eLpNorm (fun x => ‖fderiv ℝ (u n) x‖) p volume ≤ ENNReal.ofReal S) :
    ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ h : E,
      ‖h‖ < δ →
      eLpNorm (fun x => u n (x - h) - u n x) p volume ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := max S 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hSC : S ≤ C := (le_max_left S 0).trans (by dsimp [C]; linarith)
  refine ⟨ε / C, div_pos hε hC, fun n h hh => ?_⟩
  have htranslate :=
    eLpNorm_translate_sub_le_smul_eLpNorm_fderiv hp_one hp_top (hu_smooth n) h
  have hsym :
      eLpNorm (fun x => u n (x - h) - u n x) p volume =
        eLpNorm (fun x => u n x - u n (x - h)) p volume :=
    eLpNorm_sub_comm (fun x => u n (x - h)) (u n) p volume
  rw [hsym]
  calc
    _ ≤ ENNReal.ofReal ‖h‖ *
        eLpNorm (fun x => ‖fderiv ℝ (u n) x‖) p volume := htranslate
    _ ≤ ENNReal.ofReal ‖h‖ * ENNReal.ofReal C :=
      mul_le_mul' le_rfl ((hu_deriv n).trans (ENNReal.ofReal_le_ofReal hSC))
    _ = ENNReal.ofReal (‖h‖ * C) := (ENNReal.ofReal_mul (norm_nonneg h)).symm
    _ ≤ ENNReal.ofReal ε :=
      ENNReal.ofReal_le_ofReal ((lt_div_iff₀ hC).mp hh).le

/-- Smooth functions supported in a common compact set and uniformly bounded in
the first-order `L^p` norm have an `L^p` convergent subsequence. -/
theorem rellich_smooth_common_compact_support
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {K : Set E} (hK : IsCompact K)
    {u : ℕ → E → ℝ}
    (hu_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n))
    (hu_support : ∀ n, tsupport (u n) ⊆ K)
    {R S : ℝ}
    (hu_bound : ∀ n, eLpNorm (u n) p volume ≤ ENNReal.ofReal R)
    (hu_deriv : ∀ n,
      eLpNorm (fun x => ‖fderiv ℝ (u n) x‖) p volume ≤ ENNReal.ofReal S) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ (v : E → ℝ),
      MemLp v p volume ∧
      Tendsto (fun k => eLpNorm (fun x => u (φ k) x - v x) p volume)
        atTop (𝓝 0) := by
  have hu_mem : ∀ n, MemLp (u n) p volume := fun n =>
    (hu_smooth n).continuous.memLp_of_hasCompactSupport
      (hK.of_isClosed_subset (isClosed_tsupport _) (hu_support n))
  apply tendsto_subseq_of_uniform_translation_in_Lp hp_one hp_top hK hu_mem
    (fun n x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hu_support n h))
    hu_bound
  exact uniform_translation_of_eLpNorm_fderiv_le hp_one hp_top hu_smooth hu_deriv

/-- The `L^2` Rellich theorem in the square-integral form used by energy estimates. -/
theorem rellich_smooth_common_compact_support_integral_sq
    {K : Set E} (hK : IsCompact K)
    {u : ℕ → E → ℝ}
    (hu_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n))
    (hu_support : ∀ n, tsupport (u n) ⊆ K)
    {R S : ℝ}
    (hu_bound : ∀ n, ∫ x, u n x ^ 2 ≤ R)
    (hu_deriv : ∀ n, ∫ x, ‖fderiv ℝ (u n) x‖ ^ 2 ≤ S) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ (v : E → ℝ),
      MemLp v 2 volume ∧
      Tendsto (fun k => eLpNorm (fun x => u (φ k) x - v x) 2 volume)
        atTop (𝓝 0) := by
  have hu_compact : ∀ n, HasCompactSupport (u n) := fun n =>
    hK.of_isClosed_subset (isClosed_tsupport _) (hu_support n)
  have hu_mem : ∀ n, MemLp (u n) 2 volume := fun n =>
    (hu_smooth n).continuous.memLp_of_hasCompactSupport (hu_compact n)
  have hd_mem : ∀ n, MemLp (fun x => ‖fderiv ℝ (u n) x‖) 2 volume := fun n =>
    ((hu_smooth n).continuous_fderiv (by simp)).norm.memLp_of_hasCompactSupport
      ((hu_compact n).fderiv ℝ).norm
  exact rellich_smooth_common_compact_support (by norm_num) (by norm_num)
    hK hu_smooth hu_support
    (fun n => eLpNorm_two_le_sqrt_of_integral_sq_le (hu_mem n) (hu_bound n))
    (fun n => eLpNorm_two_le_sqrt_of_integral_sq_le (hd_mem n) (hu_deriv n))

/-- A bundled `L^2` subsequence form of smooth Rellich compactness. -/
theorem rellich_smooth_common_compact_support_cauchySeq
    {K : Set E} (hK : IsCompact K)
    {u : ℕ → E → ℝ}
    (hu_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n))
    (hu_support : ∀ n, tsupport (u n) ⊆ K)
    (hu_mem : ∀ n, MemLp (u n) 2 volume)
    {R S : ℝ}
    (hu_bound : ∀ n, ∫ x, u n x ^ 2 ≤ R)
    (hu_deriv : ∀ n, ∫ x, ‖fderiv ℝ (u n) x‖ ^ 2 ≤ S) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      CauchySeq (fun k => (hu_mem (φ k)).toLp (u (φ k))) := by
  obtain ⟨φ, hφ, v, hv, hconv⟩ :=
    rellich_smooth_common_compact_support_integral_sq hK hu_smooth hu_support
      hu_bound hu_deriv
  refine ⟨φ, hφ, ?_⟩
  apply Filter.Tendsto.cauchySeq (x := hv.toLp v)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hconv' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  simpa only [Function.comp_def, ENNReal.toReal_zero, ← MemLp.toLp_sub,
    Lp.norm_toLp, Pi.sub_def] using hconv'

end Poincare.Analysis.Sobolev
