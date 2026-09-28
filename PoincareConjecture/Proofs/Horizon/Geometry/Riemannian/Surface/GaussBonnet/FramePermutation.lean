import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.AdjacentFrames
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Orientation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Permutation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle Matrix

namespace PoincareConjecture.Topology.Surface

def trianglePermutationOrientation (r : Equiv.Perm (Fin 3)) : ℝ :=
  let v := standardTriangleVertex (r.symm 1) - standardTriangleVertex (r.symm 0)
  let w := standardTriangleVertex (r.symm 2) - standardTriangleVertex (r.symm 0)
  v.1 * w.2 - v.2 * w.1

theorem trianglePermutationOrientation_sq (r : Equiv.Perm (Fin 3)) :
    trianglePermutationOrientation r ^ 2 = 1 := by
  have h01 : r.symm 0 ≠ r.symm 1 := r.symm.injective.ne (by decide)
  have h02 : r.symm 0 ≠ r.symm 2 := r.symm.injective.ne (by decide)
  have h12 : r.symm 1 ≠ r.symm 2 := r.symm.injective.ne (by decide)
  unfold trianglePermutationOrientation
  generalize h0 : r.symm 0 = i at *
  generalize h1 : r.symm 1 = j at *
  generalize h2 : r.symm 2 = k at *
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [standardTriangleVertex] at *

theorem trianglePermutationOrientation_cyclic (k : Fin 3) :
    trianglePermutationOrientation (Equiv.addRight k) = 1 := by
  fin_cases k <;> norm_num [trianglePermutationOrientation, standardTriangleVertex,
    Equiv.addRight, Fin.neg_def, Fin.add_def, Matrix.cons_val]
  rfl

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem coordinateTriangle_frameOrientation_reindex_zero
    (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (r : Equiv.Perm (Fin 3))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    (R : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F (b.reindex r))) :
    let x := F (b (r.symm 0))
    g.frameOrientation x (Q.first x) (Q.second x) (R.first x) (R.second x) =
      trianglePermutationOrientation r := by
  let x := F (b (r.symm 0))
  let e := coordinateTriangleChart F b
  let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0)) x
  let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1)) x
  let v := standardTriangleVertex (r.symm 1) - standardTriangleVertex (r.symm 0)
  let w := standardTriangleVertex (r.symm 2) - standardTriangleVertex (r.symm 0)
  let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => v) x
  let W := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => w) x
  have hx : x ∈ F.target := F.map_source (hb (subset_convexHull ℝ _ (mem_range_self _)))
  have hxQ : x ∈ e.source := by rwa [coordinateTriangleChart_source]
  have hxR : x ∈ (coordinateTriangleChart F (b.reindex r)).source := by
    rwa [coordinateTriangleChart_source]
  have hbr : convexHull ℝ (range (b.reindex r)) ⊆ F.source := by
    simpa only [AffineBasis.coe_reindex, EquivLike.range_comp] using hb
  have hposR := coordinateFrame_positive_at_zero F (b.reindex r) hF hFi hbr g R
  rw [coordinateTriangleVelocity_reindex, coordinateTriangleVelocity_reindex,
    coordinateTriangleVelocity_eq_chartField F b hF hFi hb,
    coordinateTriangleVelocity_eq_chartField F b hF hFi hb] at hposR
  change 0 < g.frameOrientation x (R.first x) (R.second x) V W at hposR
  let P := g.frameOrientation x (Q.first x) (Q.second x) X Y
  let N := g.frameOrientation x (R.first x) (R.second x) V W
  let δ := g.frameOrientation x (Q.first x) (Q.second x) (R.first x) (R.second x)
  have hP : 0 < P := Q.positive x hxQ
  have hN : 0 < N := hposR
  have hd : N * δ = P * trianglePermutationOrientation r := by
    rw [← g.frameOrientation_change x (Q.first x) (Q.second x)
      (R.unit_first x hxR) (R.unit_second x hxR) (R.orthogonal x hxR) V W]
    rw [show V = v.1 • X + v.2 • Y from chartField_eq_coordinates e x v,
      show W = w.1 • X + w.2 • Y from chartField_eq_coordinates e x w]
    simp only [P, RiemannianMetric.frameOrientation, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul, trianglePermutationOrientation, v, w]
    ring
  have hδ : δ ^ 2 = 1 := g.frameOrientation_sq x
    (Q.unit_first x hxQ) (Q.unit_second x hxQ) (Q.orthogonal x hxQ)
    (R.unit_first x hxR) (R.unit_second x hxR) (R.orthogonal x hxR)
  have hκ := trianglePermutationOrientation_sq r
  change δ = trianglePermutationOrientation r
  rcases sq_eq_one_iff.mp hδ with hδ | hδ <;>
    rcases sq_eq_one_iff.mp hκ with hκ | hκ <;> nlinarith

theorem coordinateTriangle_frameOrientation_reindex
    (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (r : Equiv.Perm (Fin 3))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    (R : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F (b.reindex r))) :
    ∀ z ∈ convexHull ℝ (range b),
      g.frameOrientation (F z) (Q.first (F z)) (Q.second (F z))
        (R.first (F z)) (R.second (F z)) = trianglePermutationOrientation r := by
  have hsQ : (coordinateTriangleChart F b).source = F.target := coordinateTriangleChart_source F b
  have hsR : (coordinateTriangleChart F (b.reindex r)).source = F.target :=
    coordinateTriangleChart_source F (b.reindex r)
  obtain ⟨δ, _, hδ⟩ := g.exists_frameOrientation_sign_on_curve
    (hsQ ▸ Q.smooth_first) (hsQ ▸ Q.smooth_second)
    (hsR ▸ R.smooth_first) (hsR ▸ R.smooth_second)
    (hsQ ▸ Q.unit_first) (hsQ ▸ Q.unit_second) (hsQ ▸ Q.orthogonal)
    (hsR ▸ R.unit_first) (hsR ▸ R.unit_second) (hsR ▸ R.orthogonal)
    (convex_convexHull ℝ (range b)).isPreconnected (F.continuousOn.mono hb)
    (fun _ hz => F.map_source (hb hz))
  have hzero := coordinateTriangle_frameOrientation_reindex_zero g F b r hF hFi hb Q R
  dsimp only at hzero
  rw [hδ _ (subset_convexHull ℝ _ (mem_range_self (r.symm 0)))] at hzero
  intro z hz
  exact (hδ z hz).trans hzero

theorem surfaceTurningForm_coordinate_reindex
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (r : Equiv.Perm (Fin 3))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    (R : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F (b.reindex r)))
    (T V : (x : S) → TangentSpace (𝓡 2) x)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ convexHull ℝ (range b)) :
    D.surfaceTurningForm R.first R.second T V (F z) =
      trianglePermutationOrientation r * D.surfaceTurningForm Q.first Q.second T V (F z) := by
  have hx : F z ∈ (coordinateTriangleChart F b).source := by
    rw [coordinateTriangleChart_source]
    exact F.map_source (hb hz)
  rw [D.surfaceTurningForm_change_frame Q.first Q.second R.first R.second T V (F z)
    (Q.unit_first _ hx) (Q.unit_second _ hx) (Q.orthogonal _ hx)]
  change g.frameOrientation (F z) (Q.first (F z)) (Q.second (F z))
    (R.first (F z)) (R.second (F z)) * _ = _
  rw [coordinateTriangle_frameOrientation_reindex g F b r hF hFi hb Q R z hz]

end PoincareConjecture.Topology.Surface
