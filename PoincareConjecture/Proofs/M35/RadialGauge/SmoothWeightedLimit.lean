import PoincareConjecture.Proofs.M35.RadialGauge.SmoothLimit

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem smooth_limit_preserves_weighted_jet_bound
    {f : ℕ → V → ℝ} {u : V → ℝ} {C : ℕ → ℝ} {w : V → ℝ} {J : ℝ} (m : ℕ)
    (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hb : ∀ j k x, ‖iteratedFDeriv ℝ j (f k) x‖ ≤ C j)
    (hu : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (u x)))
    (hw : ∀ k x, w x * ‖iteratedFDeriv ℝ m (f k) x‖ ≤ J) :
    ∀ x, w x * ‖iteratedFDeriv ℝ m u x‖ ≤ J := by
  obtain ⟨L⟩ := Poincare.Analysis.Calculus.exists_smoothSubsequenceExtraction
    (Ω := univ) isOpen_univ f (fun k => (hf k).contDiffOn)
    (fun _ _ _ j => ⟨C j, Eventually.of_forall (fun k x _ => hb j k x)⟩)
  have heq : L.limit = u := by
    funext x
    have h0 := (L.iteratedFDeriv_tendsto_uniformlyOn 0 {x}
      (isCompact_singleton (x := x)) (subset_univ _)).tendsto_at (mem_singleton x)
    have hL : Tendsto (fun k => f (L.subsequence k) x) atTop (𝓝 (L.limit x)) := by
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
        LinearIsometryEquiv.apply_symm_apply] using
        (continuousMultilinearCurryFin0 ℝ V ℝ).continuous.continuousAt.tendsto.comp h0
    exact tendsto_nhds_unique hL ((hu x).comp L.subsequence_strictMono.tendsto_atTop)
  intro x
  rw [← heq]
  have hjet := (L.iteratedFDeriv_tendsto_uniformlyOn m {x}
    (isCompact_singleton (x := x)) (subset_univ _)).tendsto_at (mem_singleton x)
  exact le_of_tendsto (hjet.norm.const_mul (w x))
    (Eventually.of_forall (fun k => hw (L.subsequence k) x))

end PoincareConjecture.M35.RadialGauge
