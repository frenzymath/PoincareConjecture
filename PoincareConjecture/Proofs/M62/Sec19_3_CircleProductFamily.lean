import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductMetric
import PoincareConjecture.Proofs.M62.Mathlib.InducedMetricFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem circleProductMetric_isSmoothFamilyOn
    (F : RicciFlow n M (Set.Icc a b)) {p : ℝ} (C : CircleGeometry p)
    (P : CircleProductCharts C n M)
    (G : ℝ → RiemannianMetric (n + 1) P.Point)
    (hG : ∀ (t : ℝ) (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
      (G t).inner q V W =
        (F.metric t).inner q.1 (P.split q V).1 (P.split q W).1 +
          C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2) :
    RiemannianMetric.IsSmoothFamilyOn G (Set.Icc a b) := by
  let := P.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.Point → M) :=
    contMDiff_fst.comp P.to_product_smooth
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) ∞ (Prod.snd : P.Point → C.Point) :=
    contMDiff_snd.comp P.to_product_smooth
  have hcircle : RiemannianMetric.IsSmoothFamilyOn
      (fun _ : ℝ => C.metricOnPoints) (Set.Icc a b) :=
    (C.metricOnPoints.contMDiff.comp contMDiff_snd).contMDiffOn
  have hfirst := Poincare.Gluing.inducedForm_family_contMDiffOn F.smooth hfst
  have hsecond := Poincare.Gluing.inducedForm_family_contMDiffOn
    (I := 𝓡 (n + 1)) (J := 𝓡 1) (g := fun _ => C.metricOnPoints)
    (S := Set.Icc a b) hcircle hsnd
  have hform (t : ℝ) (q : P.Point) : (G t).inner q =
      Poincare.Gluing.inducedForm (I := 𝓡 (n + 1)) (F.metric t) Prod.fst q +
        Poincare.Gluing.inducedForm (I := 𝓡 (n + 1)) C.metricOnPoints Prod.snd q := by
    ext V W
    rw [hG]
    change _ = (F.metric t).inner q.1
        (mfderiv (𝓡 (n + 1)) (𝓡 n) Prod.fst q V)
        (mfderiv (𝓡 (n + 1)) (𝓡 n) Prod.fst q W) +
      C.metricOnPoints.inner q.2
        (mfderiv (𝓡 (n + 1)) (𝓡 1) Prod.snd q V)
        (mfderiv (𝓡 (n + 1)) (𝓡 1) Prod.snd q W)
    rw [← P.split_space, ← P.split_space, ← P.split_circle, ← P.split_circle]
  intro z hz
  have h1 := hfirst z hz
  have h2 := hsecond z hz
  rw [contMDiffWithinAt_hom_bundle] at h1 h2 ⊢
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  convert! h1.2.add h2.2 using 1
  funext y
  simp only [ContinuousLinearMap.inCoordinates, Pi.add_apply]
  rw [hform y.1 y.2]
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

end PoincareConjecture.M62
