import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.LinearGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.RegularBand

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

theorem exists_smooth_exhaustion_approx_with_uniform_radial_gap
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let f := busemannExhaustion p
    ∃ l : ℝ, 0 < l ∧ ∀ b : ℝ, 1 ≤ b →
      let U := {x | 1 / 2 < f x ∧ f x < b + 1 / 2}
      ∃ lb : ℝ, 0 < lb ∧ IsOpen U ∧
        ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ (u : M → ℝ) (H : ℝ),
          0 < H ∧ H ≤ η ∧ ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧ u p ≤ ε ∧
          (∀ x ∈ horoballIntersection p (b + 1), u x ≤ f x + ε) ∧
          (∀ x ∈ horoballIntersection p (b + 1), 0 < f x → |u x - f x| ≤ ε) ∧
          (∀ x ∈ horoballIntersection p (b + 1),
            g.tangentNorm x (D.gradient u x) ≤ 2) ∧
          (∀ x ∈ horoballIntersection p (b + 1), ∀ v : TangentSpace (𝓡 n) x,
            -H * g.inner x v v ≤ D.hessian u x v v) ∧
          (∀ x ∈ U, lb ≤ g.tangentNorm x (D.gradient u x)) ∧
          IsCompact {x | x ∈ U ∧ u x ∈ Icc 1 b} ∧
          ∀ x ∈ horoballIntersection p (b + 1), 1 ≤ f x →
            H * (g.edist x p).toReal ≤ 2 * l ∧
            2 * l * (g.edist x p).toReal ≤ u x - u p := by
  letI := g.toMetricSpace
  let f := busemannExhaustion p
  obtain ⟨R, hR, hlinear⟩ := g.exists_distance_le_mul_busemannExhaustion D hc hsec p
  let l := 1 / (8 * R)
  have hl : 0 < l := by dsimp [l]; positivity
  have hlR : 2 * l * R = 1 / 4 := by dsimp [l]; field_simp; ring
  refine ⟨l, hl, ?_⟩
  intro b hb
  have hbpos : 0 < b + 1 := by linarith
  obtain ⟨lb, hlb, hU, hsmooth⟩ :=
    g.exists_smooth_exhaustion_approx_with_regular_band_controls D hc hsec p zero_lt_one hb
  refine ⟨lb, hlb, hU, ?_⟩
  intro ε η hε hη
  let e := min ε (1 / 8)
  have he : 0 < e := lt_min hε (by norm_num)
  have heε : e ≤ ε := min_le_left _ _
  have heighth : e ≤ 1 / 8 := min_le_right _ _
  let H := min η (min 1 (l / (R * (b + 1))))
  have hH : 0 < H := lt_min hη (lt_min zero_lt_one (by positivity))
  have hHη : H ≤ η := min_le_left _ _
  have hHone : H ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hHR : H * (R * (b + 1)) ≤ l :=
    (le_div_iff₀ (mul_pos hR hbpos)).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨u, hu, hup, hupper, herror, hgradupper, hhess, hgrad, hband⟩ :=
    hsmooth e H he hH
  refine ⟨u, H, hH, hHη, hu, hup.trans heε, ?_, ?_, ?_, hhess, hgrad, hband, ?_⟩
  · intro x hx
    exact (hupper x hx).trans (add_le_add_right heε _)
  · intro x hx hpos
    exact (herror x hx hpos).trans heε
  · intro x hx
    exact (hgradupper x hx).trans (by linarith)
  · intro x hx hfx
    have hd : (g.edist x p).toReal ≤ R * f x := by
      change dist x p ≤ R * f x
      rw [dist_comm]
      exact hlinear x hfx
    have hfxb : f x ≤ b + 1 := (busemannExhaustion_le_iff hbpos.le).mpr hx
    have hdist := hd.trans (mul_le_mul_of_nonneg_left hfxb hR.le)
    refine ⟨(mul_le_mul_of_nonneg_left hdist hH.le).trans (hHR.trans (by linarith)), ?_⟩
    have hscaled := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * l by positivity)
    rw [← mul_assoc, hlR] at hscaled
    have herr := (abs_le.mp (herror x hx (zero_lt_one.trans_le hfx))).1
    change -e ≤ u x - f x at herr
    linarith

end PoincareConjecture.RiemannianMetric
