import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.Riemannian.Comparison.Covering

/-!
# Finite covers inside a bounded radial margin

An upper volume bound on a slightly larger ball and lower volume bounds at
every covering center give a finite cover without enlarging the controlled
radius by a fixed factor. This is the packing step of Morgan--Tian
Theorem 5.6, printed pp. 85-87; see the bounded-margin factory derivation
dated 2026-09-22 under tasks/M28/partial-geometry.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal Manifold ContDiff Bundle

universe u

namespace PoincareMT.M28

/-- Local lower ball volumes and a containing upper volume bound produce
an internal finite cover with a parameter-only cardinality bound. No
completeness or fivefold radius enlargement is used; Theorem 5.6, pp. 85-87. -/
theorem exists_finset_cover_of_local_volume_bounds
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) {r S δ v V : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hmargin : r + δ / 2 ≤ S)
    (hv : 0 < v) (hV : 0 ≤ V)
    (hupper : g.volumeMeasure (g.ball p S) ≤ ENNReal.ofReal V)
    (hlower : ∀ q ∈ g.ball p r,
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball q (δ / 2))) :
    ∃ C : Finset M, (↑C : Set M) ⊆ g.ball p r ∧ C.card ≤ ⌈V / v⌉₊ ∧
      g.ball p r ⊆ ⋃ q ∈ C, g.ball q δ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hball (q : M) (s : ℝ) : Metric.eball q (ENNReal.ofReal s) = g.ball q s := by
    ext y
    change g.edist y q < ENNReal.ofReal s ↔ g.edist q y < ENNReal.ofReal s
    rw [show g.edist y q = g.edist q y from Manifold.riemannianEDist_comm]
  have hfinite : g.volumeMeasure (g.ball p S) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hreal : (g.volumeMeasure (g.ball p S)).toReal ≤ V := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper).trans_eq
      (ENNReal.toReal_ofReal hV)
  obtain ⟨C, hC, hcard, _hsep, hcover⟩ :=
    Poincare.exists_finset_cover_of_separated_card_le (g.ball p r)
      (ENNReal.ofReal_pos.mpr hδ) ⌈V / v⌉₊ (by
        intro C hC hsep
        have hbound := Poincare.MeasureTheory.card_le_measure_div_of_separated_balls
          g.volumeMeasure C (r := ENNReal.ofReal (δ / 2))
          (U := g.ball p S) hv hfinite (by
            intro x hx y hy hxy
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              show δ / 2 + δ / 2 = δ by ring]
            exact hsep hx hy hxy) (by
            intro x hx
            rw [hball]
            intro y hy
            change g.edist p y < ENNReal.ofReal S
            have hsum : ENNReal.ofReal r + ENNReal.ofReal (δ / 2) ≤
                ENNReal.ofReal S := by
              rw [← ENNReal.ofReal_add hr.le (half_pos hδ).le]
              exact ENNReal.ofReal_le_ofReal hmargin
            exact (Manifold.riemannianEDist_triangle.trans_lt
              (ENNReal.add_lt_add (hC hx) hy)).trans_le hsum) (by
            intro q hq
            rw [hball]
            exact hlower q (hC hq))
        exact_mod_cast (hbound.trans (div_le_div_of_nonneg_right hreal hv.le)).trans
          (Nat.le_ceil (V / v)))
  refine ⟨C, hC, hcard, ?_⟩
  intro x hx
  obtain ⟨q, hq, hxq⟩ := hcover x hx
  refine mem_iUnion₂.mpr ⟨q, hq, ?_⟩
  change g.edist q x < ENNReal.ofReal δ
  change g.edist x q < ENNReal.ofReal δ at hxq
  simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hxq

end PoincareMT.M28
