import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ChartLimit

set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

theorem m65Projected_tendsto_continuousMap
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Icc a b)}
    (hcompact : IsCompact (univ : Set M)) {circumference : ℕ → ℝ}
    (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k))
    {r s C B₀ B₁ : ℝ} (hrs : r ≤ s) (hsub : Icc r s ⊆ Ioo a b)
    (hC : 0 ≤ C) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hRm : ∀ t ∈ Icc r s, ∀ q : M, (F.connection t).curvatureTensorNorm q ≤ C)
    (hv : ∀ k t x, t ∈ Icc r s → curveSpeed (P k).flow (c k) t x ≤ B₀)
    (hcurv : ∀ k t x, t ∈ Icc r s → m62Curvature (P k).flow (c k) t x ≤ B₁)
    (q : C((Ioo r s ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)), M))
    (hpoint : ∀ z : (Ioo r s ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)),
      Tendsto (fun k => (c k z.1.2 z.1.1).1) atTop (𝓝 (q z))) :
    Tendsto (fun k => m65ProjectedContinuousMap (P k) (c k) (hc k) hsub)
      atTop (𝓝 q) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, q', hq'⟩ := m65Projected_exists_continuous_subsequence
    hcompact (fun k => P (ns k)) (fun k => c (ns k)) (fun k => hc (ns k))
    hrs hsub hC hB₀ hB₁ hRm (fun k => hv (ns k)) (fun k => hcurv (ns k))
  have heq : q' = q := by
    ext z
    have h1 := ((continuous_eval_const z).tendsto q').comp hq'
    have h2 := (hpoint z).comp (hns.comp hms.tendsto_atTop)
    exact tendsto_nhds_unique h1 h2
  exact ⟨ms, heq ▸ hq'⟩

end PoincareConjecture
