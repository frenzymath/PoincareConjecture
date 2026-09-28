import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.GradientGap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_smooth_exhaustion_approx_with_regular_band_controls
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    letI := g.toMetricSpace
    let f := busemannExhaustion p
    let U := {x | a / 2 < f x ∧ f x < b + 1 / 2}
    ∃ l : ℝ, 0 < l ∧ IsOpen U ∧
      ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ u : M → ℝ,
        ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧ u p ≤ ε ∧
        (∀ x ∈ horoballIntersection p (b + 1), u x ≤ f x + ε) ∧
        (∀ x ∈ horoballIntersection p (b + 1), 0 < f x → |u x - f x| ≤ ε) ∧
        (∀ x ∈ horoballIntersection p (b + 1),
          g.tangentNorm x (D.gradient u x) ≤ 1 + η) ∧
        (∀ x ∈ horoballIntersection p (b + 1), ∀ v : TangentSpace (𝓡 n) x,
          -η * g.inner x v v ≤ D.hessian u x v v) ∧
        (∀ x ∈ U, l ≤ g.tangentNorm x (D.gradient u x)) ∧
        IsCompact {x | x ∈ U ∧ u x ∈ Icc a b} := by
  letI := g.toMetricSpace
  let f := busemannExhaustion p
  let U := {x | a / 2 < f x ∧ f x < b + 1 / 2}
  let C := horoballIntersection p (b + 1)
  have hb : 0 < b := ha.trans_le hab
  have hf : Continuous f := (lipschitz_busemannExhaustion p).continuous
  have hU : IsOpen U := (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
  have hC : IsCompact C :=
    g.isCompact_horoballIntersection_of_nonnegativeSectional D hc hsec hdist p (by linarith)
  have hp : p ∈ C := closedBall_subset_horoballIntersection p (b + 1)
    (by simp only [mem_closedBall, dist_self]; linarith)
  have hconvex : ∀ (γ : ℝ → M) (s t : ℝ), g.IsGeodesicOn γ (Icc s t) →
      γ s ∈ C → γ t ∈ C → MapsTo γ (Icc s t) C := by
    intro γ s t hγ hs ht
    exact mapsTo_horoballIntersection_of_concaveOn
      (fun ray hray _ => g.concaveOn_busemann_of_nonnegativeSectional
        D hc hsec hdist hray hγ) hs ht
  have hUC : U ⊆ C := by
    intro x hx
    apply (busemannExhaustion_le_iff (by linarith : 0 ≤ b + 1)).mp
    change a / 2 < f x ∧ f x < b + 1 / 2 at hx
    change f x ≤ b + 1
    linarith [hx.2]
  obtain ⟨R, hR, _, hgradient⟩ := D.exists_uniform_gradient_bound_of_compact_totallyConvex
    hc hC hconvex hp (show 0 < a / 4 by positivity)
  let l := (a / 4) / (2 * R)
  have hl : 0 < l := by dsimp [l]; positivity
  refine ⟨l, hl, hU, ?_⟩
  intro ε η hε hη
  let e := min ε (min (a / 8) (1 / 8))
  have he : 0 < e := lt_min hε (lt_min (by positivity) (by norm_num))
  have heε : e ≤ ε := min_le_left _ _
  have hea : e ≤ a / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have heone : e ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  let H := min η ((a / 4) / R ^ 2)
  have hH : 0 < H := lt_min hη (div_pos (by positivity) (sq_pos_of_pos hR))
  have hHη : H ≤ η := min_le_left _ _
  have hHR : H * R ^ 2 ≤ a / 4 :=
    (le_div_iff₀ (sq_pos_of_pos hR)).mp (min_le_right _ _)
  obtain ⟨u, hu, hup, hupper, herror, hgradupper, hhess⟩ :=
    g.exists_smooth_exhaustion_approx_on_compact D hc hsec p hC he hH
  have hgrad (x : M) (hx : x ∈ U) : l ≤ g.tangentNorm x (D.gradient u x) := by
    apply hgradient u hu H hH.le hHR hhess x (hUC hx)
    have hpos : 0 < f x := (by positivity : 0 < a / 2).trans hx.1
    have hlow := (abs_le.mp (herror x (hUC hx) hpos)).1
    change -(min ε (min (a / 8) (1 / 8))) ≤ u x - f x at hlow
    change u p ≤ e at hup
    change a / 2 < f x ∧ f x < b + 1 / 2 at hx
    dsimp only [e] at hea
    linarith [hx.1]
  have hbandset : {x | x ∈ U ∧ u x ∈ Icc a b} = C ∩ u ⁻¹' Icc a b := by
    ext x
    constructor
    · intro hx
      exact ⟨hUC hx.1, hx.2⟩
    · rintro ⟨hxC, hxu⟩
      have hsup := hupper x hxC
      change u x ≤ f x + e at hsup
      have hlow : a / 2 < f x := by linarith [hxu.1]
      have herr := (abs_le.mp (herror x hxC ((by positivity : 0 < a / 2).trans hlow))).1
      change -e ≤ u x - f x at herr
      refine ⟨⟨hlow, ?_⟩, hxu⟩
      linarith [hxu.2]
  refine ⟨u, hu, hup.trans heε, ?_, ?_, ?_, ?_, hgrad, ?_⟩
  · intro x hx
    exact (hupper x hx).trans (add_le_add_right heε _)
  · intro x hx hpos
    exact (herror x hx hpos).trans heε
  · intro x hx
    exact (hgradupper x hx).trans (add_le_add_right hHη 1)
  · intro x hx v
    have hi : 0 ≤ g.inner x v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (g.pos x v hv).le
    exact (mul_le_mul_of_nonneg_right (neg_le_neg hHη) hi).trans (hhess x hx v)
  · rw [hbandset]
    exact hC.inter_right (isClosed_Icc.preimage hu.continuous)

theorem exists_smooth_exhaustion_approx_with_regular_band
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    letI := g.toMetricSpace
    let f := busemannExhaustion p
    let U := {x | a / 2 < f x ∧ f x < b + 1 / 2}
    ∃ l : ℝ, 0 < l ∧ IsOpen U ∧
      ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ u : M → ℝ,
        ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧ u p ≤ ε ∧
        (∀ x ∈ horoballIntersection p (b + 1), u x ≤ f x + ε) ∧
        (∀ x ∈ horoballIntersection p (b + 1), 0 < f x → |u x - f x| ≤ ε) ∧
        (∀ x ∈ U, l ≤ g.tangentNorm x (D.gradient u x)) ∧
        (∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
          -η * g.inner x v v ≤ D.hessian u x v v) ∧
        IsCompact {x | x ∈ U ∧ u x ∈ Icc a b} := by
  letI := g.toMetricSpace
  obtain ⟨l, hl, hU, hsmooth⟩ :=
    g.exists_smooth_exhaustion_approx_with_regular_band_controls D hc hsec p ha hab
  refine ⟨l, hl, hU, ?_⟩
  intro ε η hε hη
  obtain ⟨u, hu, hup, hupper, herror, _, hhess, hgrad, hband⟩ := hsmooth ε η hε hη
  refine ⟨u, hu, hup, hupper, herror, hgrad, ?_, hband⟩
  intro x hx v
  apply hhess x ?_ v
  apply (busemannExhaustion_le_iff (by linarith : 0 ≤ b + 1)).mp
  linarith [hx.2]

end PoincareConjecture.RiemannianMetric
