import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductCharts
import PoincareConjecture.Proofs.M01.NormalizationMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.InducedForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_circleProductMetric
    (g : RiemannianMetric n M) {p : ℝ} (C : CircleGeometry p)
    (P : CircleProductCharts C n M) :
    ∃ G : RiemannianMetric (n + 1) P.Point,
      ∀ (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
        G.inner q V W =
          g.inner q.1 (P.split q V).1 (P.split q W).1 +
            C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2 := by
  let := P.chartedSpace
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let Q : (q : P.Point) → TangentSpace (𝓡 (n + 1)) q →L[ℝ]
      TangentSpace (𝓡 (n + 1)) q →L[ℝ] ℝ := fun q =>
    Poincare.Gluing.inducedForm (I := 𝓡 (n + 1)) g Prod.fst q +
      Poincare.Gluing.inducedForm (I := 𝓡 (n + 1)) C.metricOnPoints Prod.snd q
  have hQ (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q) :
      Q q V W = g.inner q.1 (P.split q V).1 (P.split q W).1 +
        C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2 := by
    change g.inner q.1
        (mfderiv (𝓡 (n + 1)) (𝓡 n) Prod.fst q V)
        (mfderiv (𝓡 (n + 1)) (𝓡 n) Prod.fst q W) +
      C.metricOnPoints.inner q.2
        (mfderiv (𝓡 (n + 1)) (𝓡 1) Prod.snd q V)
        (mfderiv (𝓡 (n + 1)) (𝓡 1) Prod.snd q W) = _
    rw [← P.split_space, ← P.split_space, ← P.split_circle, ← P.split_circle]
  have hpos (q : P.Point) (V : TangentSpace (𝓡 (n + 1)) q) (hV : V ≠ 0) :
      0 < Q q V V := by
    rw [hQ]
    by_cases hs : (P.split q V).1 = 0
    · have ht : (P.split q V).2 ≠ 0 := by
        intro ht
        apply hV
        apply (P.split q).injective
        ext <;> simp [hs, ht]
      simpa only [hs, map_zero, zero_apply, zero_add] using
        C.metricOnPoints.pos q.2 _ ht
    · exact add_pos_of_pos_of_nonneg (g.pos q.1 _ hs)
        (by
          by_cases ht : (P.split q V).2 = 0
          · simp only [ht, map_zero, le_refl]
          · exact (C.metricOnPoints.pos q.2 _ ht).le)
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.Point → M) :=
    contMDiff_fst.comp P.to_product_smooth
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) ∞ (Prod.snd : P.Point → C.Point) :=
    contMDiff_snd.comp P.to_product_smooth
  refine ⟨{
    inner := Q
    symm := fun q V W => by rw [hQ, hQ, g.symm, C.metricOnPoints.symm]
    pos := hpos
    isVonNBounded := fun q => m01_isVonNBounded_of_posDef (F := E) (Q q) (hpos q)
    contMDiff := ?_
  }, hQ⟩
  intro q
  exact (Poincare.Gluing.inducedForm_contMDiffAt g (hfst q)).add_section
    (Poincare.Gluing.inducedForm_contMDiffAt C.metricOnPoints (hsnd q))

end PoincareConjecture.M62
