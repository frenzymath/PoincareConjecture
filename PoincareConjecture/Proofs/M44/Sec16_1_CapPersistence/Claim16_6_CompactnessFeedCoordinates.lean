import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.FiniteDimensional
import PoincareConjecture.Proofs.M44.Mathlib.CompactSmoothConvergence











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M44

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]





theorem exists_common_coordinate_limit
    {U : ℕ → Set E} (hU : ∀ i, IsOpen (U i)) (f : ℕ → E → V)
    (hsmooth : ∀ i, ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) (U i))
    (hbound : ∀ i K, IsCompact K → K ⊆ U i → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (f k) x‖ ≤ B) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∃ b : ℕ → E → V,
      ∀ i, CompactSmoothConvergenceOn (fun k => f (sigma k)) (b i) atTop (U i) := by
  classical
  let patched (i k : ℕ) : E → V :=
    if ContDiffOn ℝ ∞ (f k) (U i) then f k else fun _ => 0
  have hpatched (i k : ℕ) : ContDiffOn ℝ ∞ (patched i k) (U i) := by
    dsimp only [patched]
    split_ifs with h
    · exact h
    · exact contDiffOn_const
  have heq (i : ℕ) : ∀ᶠ k in atTop, patched i k = f k := by
    filter_upwards [hsmooth i] with k hk
    exact if_pos hk
  have hpatched_bound (i : ℕ) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U i)
      (m : ℕ) : ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (patched i k) x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hbound i K hK hKU m
    refine ⟨B, ?_⟩
    filter_upwards [heq i, hB] with k hk hBk
    simpa only [hk] using hBk
  obtain ⟨sigma, hsigma, b, hb, hjet⟩ :=
    Poincare.Analysis.Calculus.exists_common_smoothSubsequenceExtraction_finiteDimensional
      (E := fun _ => E) (F := fun _ => V) hU patched hpatched hpatched_bound
  refine ⟨sigma, hsigma, b, fun i => ⟨hU i, hb i, ?_, ?_⟩⟩
  · intro K _hK hKU
    filter_upwards [hsigma.tendsto_atTop.eventually (hsmooth i)] with k hk
    exact fun x hx => hk.contDiffAt ((hU i).mem_nhds (hKU hx))
  · intro m K hK hKU
    apply (hjet i m K hK hKU).congr
    filter_upwards [hsigma.tendsto_atTop.eventually (heq i)] with k hk
    exact fun x _ => congrArg (fun g => iteratedFDeriv ℝ m g x) hk

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in



theorem coordinate_limits_eq_on_overlap
    {f : ℕ → E → V} {b c : E → V} {U W : Set E}
    (hb : CompactSmoothConvergenceOn f b atTop U)
    (hc : CompactSmoothConvergenceOn f c atTop W) : EqOn b c (U ∩ W) := by
  intro x hx
  exact tendsto_nhds_unique
    ((hb.uniformlyOn isCompact_singleton (singleton_subset_iff.mpr hx.1)).tendsto_at
      (mem_singleton x))
    ((hc.uniformlyOn isCompact_singleton (singleton_subset_iff.mpr hx.2)).tendsto_at
      (mem_singleton x))

end PoincareConjecture.M44
