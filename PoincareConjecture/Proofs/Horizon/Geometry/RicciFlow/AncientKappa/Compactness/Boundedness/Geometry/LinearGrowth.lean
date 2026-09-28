import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import Mathlib.Analysis.Convex.Slope











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem exists_distance_le_mul_of_compact_convex_sublevel
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    (f : M → ℝ) (p : M) (hp : f p = 0)
    (hcompact : IsCompact {x | f x ≤ 1})
    (hconvex : ∀ (γ : ℝ → M) (a b : ℝ), g.IsGeodesicOn γ (Icc a b) →
      ConvexOn ℝ (Icc a b) (f ∘ γ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, 1 ≤ f x → (g.edist p x).toReal ≤ R * f x := by
  letI := g.toMetricSpace
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image (continuous_const.dist continuous_id).continuousOn
  let R := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right B 0]
  have hBR : B < R := by dsimp [R]; linarith [le_max_left B 0]
  have hsub (x : M) (hx : f x ≤ 1) : dist p x < R :=
    (hB (mem_image_of_mem (fun y => dist p y) hx)).trans_lt hBR
  refine ⟨R, hR, ?_⟩
  intro x hx
  by_contra! hlarge
  let L := (g.edist p x).toReal
  have hRL : R < L := (le_mul_of_one_le_right hR.le hx).trans_lt hlarge
  have hL : 0 < L := hR.trans hRL
  obtain ⟨γ, h0, hLend, hγ, _, hmin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hc p x hL
  change γ L = x at hLend
  have hzero : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have hRmem : R ∈ Icc 0 L := ⟨hR.le, hRL.le⟩
  have hdist : dist p (γ R) = R := by
    change (g.edist p (γ R)).toReal = R
    rw [← h0, hmin 0 hzero R hRmem]
    simp only [zero_sub, abs_neg, abs_of_pos hR, ENNReal.toReal_ofReal hR.le]
  have hvalue : 1 < f (γ R) := by
    by_contra! hsmall
    have h := hsub (γ R) hsmall
    rw [hdist] at h
    exact lt_irrefl _ h
  have hsecant := (hconvex γ 0 L hγ).secant_mono_aux1 hzero
    (show L ∈ Icc 0 L from ⟨hL.le, le_rfl⟩) hR hRL
  simp only [Function.comp_apply, h0, hLend, hp, sub_zero, mul_zero, zero_add] at hsecant
  have hstrict : L < L * f (γ R) := by nlinarith
  exact (not_lt_of_ge hsecant) (hlarge.trans hstrict)

open Poincare.Riemannian.Soul



theorem exists_distance_le_mul_busemannExhaustion
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    ∃ R : ℝ, 0 < R ∧ ∀ x, 1 ≤ busemannExhaustion p x →
      (g.edist p x).toReal ≤ R * busemannExhaustion p x := by
  letI := g.toMetricSpace
  have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
  apply g.exists_distance_le_mul_of_compact_convex_sublevel hc
    (busemannExhaustion p) p (busemannExhaustion_self p)
  · have heq : {x | busemannExhaustion p x ≤ 1} = horoballIntersection p 1 := by
      ext x
      exact busemannExhaustion_le_iff zero_le_one
    rw [heq]
    exact g.isCompact_horoballIntersection_of_nonnegativeSectional D hc hsec hdist p zero_le_one
  · intro γ a b hγ
    exact convexOn_busemannExhaustion_comp fun ray hray _ =>
      g.concaveOn_busemann_of_nonnegativeSectional D hc hsec hdist hray hγ

end PoincareConjecture.RiemannianMetric
