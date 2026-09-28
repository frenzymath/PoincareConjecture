import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv



noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff NNReal

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem exists_lipschitzOnWith_mul_exp_neg
    {C : Set E} (hC : IsCompact C) (hconv : Convex ℝ C)
    {a u : E → ℝ} (ha : ContDiffOn ℝ ∞ a C)
    {L : ℝ≥0} (hu : LipschitzOnWith L u C) :
    ∃ D : ℝ≥0, LipschitzOnWith D (fun z => a z * Real.exp (-u z)) C := by
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hu.continuousOn
  let T : Set (E × ℝ) := C ×ˢ Icc (-B) B
  let H : E × ℝ → ℝ := fun z => a z.1 * Real.exp (-z.2)
  have hH : ContDiffOn ℝ ∞ H T :=
    (ha.comp contDiffOn_fst (fun _ hz => hz.1)).mul
      (Real.contDiff_exp.comp contDiff_snd.neg).contDiffOn
  obtain ⟨D, hD⟩ := hH.exists_lipschitzOnWith (by simp)
    (hconv.prod (convex_Icc _ _)) (hC.prod isCompact_Icc)
  have hgraph : MapsTo (fun z => (z, u z)) C T := by
    intro z hz
    exact ⟨hz, abs_le.mp (hB z hz)⟩
  exact ⟨D * max 1 L, hD.comp (LipschitzWith.id.lipschitzOnWith.prodMk hu) hgraph⟩

end Poincare.Analysis
