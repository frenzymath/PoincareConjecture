import PoincareConjecture.Proofs.M08.EndpointEulerCoefficients
import PoincareConjecture.Proofs.M08.WeightedJacobiCoefficients

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J C : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)

private noncomputable local instance dualNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance dualNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

private noncomputable local instance bilinearNormedGroup :
    NormedAddCommGroup
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance bilinearNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem closedChartMomentum_contDiffOn (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} (hq : ContDiffOn ℝ ∞ q C)
    (hmap : MapsTo q C (extChartAt (𝓡 n) x).target) :
    ContDiffOn ℝ ∞ (fun s => M08.chartMomentumVector
      (M08.chartActionMetric F T x (s, q s)) (derivWithin q C s)) C := by
  have hB := M08.chartActionMetric_closed_contDiffOn F T x htime
  have hv := hq.derivWithin hC (m := ∞) (by simp)
  let L := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv
  exact L.contDiff.comp_contDiffOn ((hB.comp (contDiffOn_id.prodMk hq)
    (fun s hs => ⟨hs, hmap hs⟩)).clm_apply hv)

theorem closedChartConnection_diagonal_pair
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C)
    {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v w : EuclideanSpace ℝ (Fin n)) :
    M08.chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (M08.closedChartConnection F T x C (s, extChartAt (𝓡 n) x y) v v) w =
      M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
          (M08.chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) v v w -
        M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
          (M08.chartActionMetric F T x) (s, extChartAt (𝓡 n) x y) w v v / 2 := by
  rw [M08.chartActionMetric_apply F T hy s, M08.closedChartConnection_apply,
    ← M08.closedChartChristoffel_connection F T htime hy hs]
  exact M08.chartActionMetric_closed_connection_diagonal F T htime hy hs v w

theorem closedChartMomentum_residual_pair (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} (hq : ContDiffOn ℝ ∞ q C)
    (hmap : MapsTo q C (extChartAt (𝓡 n) x).target)
    {s : ℝ} (hs : s ∈ C) (w : EuclideanSpace ℝ (Fin n)) :
    let B := M08.chartActionMetric F T x
    let v := derivWithin q C
    let P := fun r => M08.chartMomentumVector (B (r, q r)) (v r)
    inner ℝ w (derivWithin P C s -
        M08.chartForceVector (M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target B (s, q s))
          (M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
            (M08.chartActionPotential F T x) (s, q s)) (v s)) =
      B (s, q s) (derivWithin v C s +
        M08.closedChartConnection F T x C (s, q s) (v s) (v s)) w -
        M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
          (M08.chartActionPotential F T x) (s, q s) w +
        M08.timeWithinFDeriv C (extChartAt (𝓡 n) x).target B (s, q s) (v s) w := by
  dsimp only
  let B := M08.chartActionMetric F T x
  let v := derivWithin q C
  let P := fun r => M08.chartMomentumVector (B (r, q r)) (v r)
  have hB := M08.chartActionMetric_closed_contDiffOn F T x htime
  have hv := hq.derivWithin hC (m := ∞) (by simp)
  have hPd := ((closedChartMomentum_contDiffOn F T x hC htime hq hmap) s hs)
    |>.differentiableWithinAt (by simp) |>.hasDerivWithinAt
  have hpair := M08.bilinear_curve_hasDerivWithinAt B
    ((hB (s, q s) ⟨hs, hmap hs⟩).differentiableWithinAt (by simp)).hasFDerivWithinAt
    ((hq s hs).differentiableWithinAt (by simp)).hasDerivWithinAt
    ((hv s hs).differentiableWithinAt (by simp)).hasDerivWithinAt
    (fun r hr => ⟨hr, hmap hr⟩) w
  have hinner := (innerSL ℝ w).hasFDerivAt.comp_hasDerivWithinAt s hPd
  simp only [Function.comp_def, innerSL_apply_apply, M08.chartMomentumVector_inner] at hinner
  have hd := (hinner.derivWithin (hC s hs)).symm.trans (hpair.derivWithin (hC s hs))
  have hy : (extChartAt (𝓡 n) x).symm (q s) ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target (hmap hs)
  have hdiag := closedChartConnection_diagonal_pair F T x htime hs hy (v s) w
  rw [(extChartAt (𝓡 n) x).right_inv (hmap hs)] at hdiag
  rw [inner_sub_right, M08.chartForceVector_inner, hd, map_add, add_apply, hdiag]
  dsimp only [M08.spatialWithinFDeriv, M08.timeWithinFDeriv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  ring

end PoincareConjecture.M14
