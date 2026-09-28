import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.Regularity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Covering












set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_finset_regularComponent_cover
    (g : RiemannianMetric n M) (p : M) (δ : ℝ) {r v V : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hV : 0 ≤ V)
    (hupper : g.volumeMeasure univ ≤ ENNReal.ofReal V)
    (hlower : ∀ q ∈ regularComponent g p δ,
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball q (r / 2))) :
    ∃ C : Finset M, (↑C : Set M) ⊆ regularComponent g p δ ∧
      C.card ≤ ⌈V / v⌉₊ ∧
      (↑C : Set M).Pairwise (fun x y => ENNReal.ofReal r ≤ g.edist x y) ∧
      regularComponent g p δ ⊆ ⋃ q ∈ C, g.ball q r := by
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
  have hfinite : g.volumeMeasure univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hreal : (g.volumeMeasure univ).toReal ≤ V := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper).trans_eq
      (ENNReal.toReal_ofReal hV)
  obtain ⟨C, hC, hcard, hsep, hcover⟩ :=
    Poincare.exists_finset_cover_of_separated_card_le (regularComponent g p δ)
      (ENNReal.ofReal_pos.mpr hr) ⌈V / v⌉₊ (by
        intro C hC hsep
        have hbound := Poincare.MeasureTheory.card_le_measure_div_of_separated_balls
          g.volumeMeasure C (r := ENNReal.ofReal (r / 2)) (U := univ) hv hfinite
          (by
            intro x hx y hy hxy
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              show r / 2 + r / 2 = r by ring]
            exact hsep hx hy hxy)
          (fun _ _ => subset_univ _) (by
            intro q hq
            rw [hball]
            exact hlower q (hC hq))
        exact_mod_cast (hbound.trans (div_le_div_of_nonneg_right hreal hv.le)).trans
          (Nat.le_ceil (V / v)))
  refine ⟨C, hC, hcard, hsep, ?_⟩
  intro x hx
  obtain ⟨q, hq, hxq⟩ := hcover x hx
  refine mem_iUnion₂.mpr ⟨q, hq, ?_⟩
  change g.edist q x < ENNReal.ofReal r
  change g.edist x q < ENNReal.ofReal r at hxq
  simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hxq




theorem isCompact_regularComponent_of_volume_bounds
    (g : RiemannianMetric n M) (p : M) {δ r v V : ℝ}
    (hr : 0 < r) (hrδ : r < δ) (hv : 0 < v) (hV : 0 ≤ V)
    (hupper : g.volumeMeasure univ ≤ ENNReal.ofReal V)
    (hlower : ∀ q ∈ regularComponent g p δ,
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball q (r / 2))) :
    IsCompact (regularComponent g p δ) := by
  obtain ⟨C, hC, _hcard, _hsep, hcover⟩ :=
    exists_finset_regularComponent_cover g p δ hr hv hV hupper hlower
  have hK : IsCompact (⋃ q ∈ C, closure (g.ball q r)) :=
    C.finite_toSet.isCompact_biUnion fun q hq =>
      regularComponent_subset g p δ (hC hq) r hrδ
  apply hK.of_isClosed_subset (isClosed_regularComponent g p δ)
  intro x hx
  obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hcover hx)
  exact mem_iUnion₂.mpr ⟨q, hq, subset_closure hxq⟩




theorem exists_regularComponent_cover_of_noncollapse
    (g : RiemannianMetric n M) (p : M) {δ r r₀ κ V : ℝ}
    (hr : 0 < r) (hrδ : r / 2 ≤ δ) (hr₀ : r / 2 ≤ r₀)
    (hκ : 0 < κ) (hV : 0 ≤ V)
    (hupper : g.volumeMeasure univ ≤ ENNReal.ofReal V)
    (hnoncollapse : ∀ s : ℝ, 0 < s → s ≤ r₀ → ∀ q ∈ regularComponent g p s,
      ENNReal.ofReal (κ * s ^ n) ≤ g.volumeMeasure (g.ball q s)) :
    ∃ C : Finset M, (↑C : Set M) ⊆ regularComponent g p δ ∧
      C.card ≤ ⌈V / (κ * (r / 2) ^ n)⌉₊ ∧
      (↑C : Set M).Pairwise (fun x y => ENNReal.ofReal r ≤ g.edist x y) ∧
      regularComponent g p δ ⊆ ⋃ q ∈ C, g.ball q r := by
  apply exists_finset_regularComponent_cover g p δ hr (by positivity) hV hupper
  intro q hq
  exact hnoncollapse (r / 2) (by positivity) hr₀ q
    (regularComponent_antitone g p hrδ hq)

end PoincareConjecture.M28
