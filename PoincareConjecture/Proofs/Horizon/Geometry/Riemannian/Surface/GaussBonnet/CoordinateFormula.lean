import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MetricCorners
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Frame.Chart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField MeasureTheory
open scoped Manifold ContDiff Bundle Interval
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  [MeasurableSpace S] [BorelSpace S] [T3Space S]
  {g : RiemannianMetric 2 S}

theorem gaussBonnet_coordinateTriangle_of_frame
    (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b)) :
    let e := coordinateTriangleChart F b
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (-1, 1))
    let T := fun x => (Real.sqrt (g.inner x (Y x) (Y x)))⁻¹ • Y x
    let W := fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x
    (∫ x in F '' convexHull ℝ (range b), D.scalarCurvature x ∂g.volumeMeasure) +
      2 * ((∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second Q.first X (e.symm (t, 0))) +
        (∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second W V (e.symm (1 - t, t))) -
        (∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second T Y (e.symm (0, t)))) +
      2 * (∑ i : Fin 3, (Real.pi - coordinateTriangleAngle g F b i)) =
        4 * Real.pi := by
  dsimp only
  let e := coordinateTriangleChart F b
  let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
  let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
  let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (-1, 1))
  let T := fun x => (Real.sqrt (g.inner x (Y x) (Y x)))⁻¹ • Y x
  let W := fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x
  let A := F (b 0)
  let B := F (b 1)
  let C := F (b 2)
  have hv (i : Fin 3) : e.symm (standardTriangleVertex i) = F (b i) :=
    coordinateTriangleChart_vertex F b i
  have hsrc (i : Fin 3) : F (b i) ∈ e.source := by
    rw [← hv]
    apply e.map_target
    apply coordinateTriangleChart_target F b hsource
    fin_cases i <;> norm_num [standardTriangleVertex]
  let e₁ := Q.first
  let e₂ := Q.second
  have ha (x : S) (hx : x ∈ e.source) :
      e₁ x = (Real.sqrt (g.inner x (X x) (X x)))⁻¹ • X x := Q.aligned x hx
  have hgb := D.gaussBonnet_chartTriangle_of_aligned_frame e
    (coordinateTriangleChart_smooth F b hFi)
    (coordinateTriangleChart_smooth_symm F b hF)
    Q.smooth_first Q.smooth_second Q.unit_first Q.unit_second Q.orthogonal
    (coordinateTriangleChart_target F b hsource) Q.positive Q.aligned
  have hB : Real.arccos (g.inner B (e₁ B) (W B)) =
      Real.pi - g.cornerAngle B (-X B) (V B) := by
    rw [ha B (hsrc 1), g.cornerAngle_neg_left]
    change g.cornerAngle B (X B) (V B) = _
    ring
  have hC : Real.arccos (g.inner C (W C) (-T C)) =
      Real.pi - g.cornerAngle C (-Y C) (-V C) := by
    rw [g.cornerAngle_neg_neg, g.cornerAngle_comm C (Y C) (V C)]
    simp only [T, W, RiemannianMetric.cornerAngle, map_neg, Real.arccos_neg]
  have hA : Real.arccos (g.inner A (-T A) (e₁ A)) =
      Real.pi - g.cornerAngle A (X A) (Y A) := by
    rw [ha A (hsrc 0), g.cornerAngle_comm A (X A) (Y A)]
    simp only [T, X, RiemannianMetric.cornerAngle, map_neg, neg_apply, Real.arccos_neg]
  have hang := sum_coordinateTriangleAngle_eq_chartFields g F b hF hFi hsource
  change (∑ i : Fin 3, coordinateTriangleAngle g F b i) =
    g.cornerAngle A (X A) (Y A) + g.cornerAngle B (-X B) (V B) +
      g.cornerAngle C (-Y C) (-V C) at hang
  have hsum : (∑ i : Fin 3, (Real.pi - coordinateTriangleAngle g F b i)) =
      Real.arccos (g.inner B (e₁ B) (W B)) +
      Real.arccos (g.inner C (W C) (-T C)) +
      Real.arccos (g.inner A (-T A) (e₁ A)) := by
    rw [Finset.sum_sub_distrib, hang, hA, hB, hC]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum]
  dsimp only at hgb
  rw [coordinateTriangleChart_image F b] at hgb
  have hv0 : e.symm (0, 0) = A := hv 0
  have hv1 : e.symm (1, 0) = B := hv 1
  have hv2 : e.symm (0, 1) = C := hv 2
  rw [hv0, hv1, hv2] at hgb
  exact hgb

theorem exists_gaussBonnet_coordinateTriangle
    (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source) :
    let e := coordinateTriangleChart F b
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (-1, 1))
    let T := fun x => (Real.sqrt (g.inner x (Y x) (Y x)))⁻¹ • Y x
    let W := fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x
    ∃ e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x,
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source ∧
      (∀ x ∈ e.source, g.inner x (e₁ x) (e₁ x) = 1) ∧
      (∀ x ∈ e.source, g.inner x (e₂ x) (e₂ x) = 1) ∧
      (∀ x ∈ e.source, g.inner x (e₁ x) (e₂ x) = 0) ∧
      (∀ x ∈ e.source, 0 <
        g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
          g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x)) ∧
      (∀ x ∈ e.source, e₁ x = (Real.sqrt (g.inner x (X x) (X x)))⁻¹ • X x) ∧
      (∫ x in F '' convexHull ℝ (range b), D.scalarCurvature x ∂g.volumeMeasure) +
        2 * ((∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ e₁ X (e.symm (t, 0))) +
          (∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ W V (e.symm (1 - t, t))) -
          (∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ T Y (e.symm (0, t)))) +
        2 * (∑ i : Fin 3, (Real.pi - coordinateTriangleAngle g F b i)) =
          4 * Real.pi := by
  let Q := g.alignedChartFrame (coordinateTriangleChart F b)
    (coordinateTriangleChart_smooth F b hFi)
    (coordinateTriangleChart_smooth_symm F b hF)
  exact ⟨Q.first, Q.second, Q.smooth_first, Q.smooth_second, Q.unit_first,
    Q.unit_second, Q.orthogonal, Q.positive, Q.aligned,
    D.gaussBonnet_coordinateTriangle_of_frame F b hF hFi hsource Q⟩

end PoincareConjecture.LeviCivitaData
