import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem contDiff_limit_and_uniform_jet_bounds
    {f : ℕ → V → ℝ} {u : V → ℝ} {C : ℕ → ℝ}
    (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hb : ∀ j k x, ‖iteratedFDeriv ℝ j (f k) x‖ ≤ C j)
    (hu : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (u x))) :
    ContDiff ℝ ∞ u ∧ ∀ j x, ‖iteratedFDeriv ℝ j u x‖ ≤ C j := by
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
  rw [← heq]
  refine ⟨contDiffOn_univ.mp L.limit_contDiffOn, fun j x => ?_⟩
  have hjet := (L.iteratedFDeriv_tendsto_uniformlyOn j {x}
    (isCompact_singleton (x := x)) (subset_univ _)).tendsto_at (mem_singleton x)
  exact le_of_tendsto hjet.norm (Eventually.of_forall (fun k => hb j (L.subsequence k) x))

theorem contDiff_limit_of_uniform_all_order_bounds
    {f : ℕ → V → ℝ} {u : V → ℝ}
    (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hb : ∀ j : ℕ, ∃ C : ℝ, ∀ k x, ‖iteratedFDeriv ℝ j (f k) x‖ ≤ C)
    (hu : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (u x))) : ContDiff ℝ ∞ u := by
  choose C hC using hb
  exact (contDiff_limit_and_uniform_jet_bounds hf hC hu).1

end PoincareConjecture.M35.RadialGauge
