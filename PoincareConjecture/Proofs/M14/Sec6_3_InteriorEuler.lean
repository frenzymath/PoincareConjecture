import PoincareConjecture.Proofs.M14.Sec6_3_InteriorPotential
import PoincareConjecture.Proofs.M09.CoordinateEulerLinearization










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)




theorem closedChartEulerPair_velocityPhase
    (hM04 : RicciFlowCurvatureTheory.{u}) {C : Set ℝ}
    (htime : ∀ r ∈ C, T - r ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C) (hnear : C ∈ 𝓝 s)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target)
    (v a : EuclideanSpace ℝ (Fin n))
    (heuler : ∀ W : EuclideanSpace ℝ (Fin n),
      M08.chartActionMetric F T x (s, q)
          (a + M08.closedChartConnection F T x C (s, q) v v) W -
        M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
          (M08.chartActionPotential F T x) (s, q) W +
        M08.timeWithinFDeriv C (extChartAt (𝓡 n) x).target
          (M08.chartActionMetric F T x) (s, q) v W = 0) :
    a = (Proofs.M09.regularizedCoordinatePhase
      (M08.chartActionMetric F T x) (chartActionScalar F T x) (s, (q, v))).2 := by
  let B := M08.chartActionMetric F T x
  let R := chartActionScalar F T x
  let alpha := (Proofs.M09.regularizedCoordinatePhase B R (s, (q, v))).2
  have ht : M08.timeWithinFDeriv C (extChartAt (𝓡 n) x).target B (s, q) =
      fderiv ℝ B (s, q) (1, 0) := by
    unfold M08.timeWithinFDeriv
    rw [fderivWithin_of_mem_nhds
      (prod_mem_nhds hnear ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds hq))]
  have hp : B (s, q) a = B (s, q) alpha := by
    ext W
    have he := heuler W
    rw [closedChartConnection_eq_open F T x hnear hq,
      chartActionPotential_spatialWithin_eq F T x hM04 htime hs hnear hq, ht] at he
    have ho := Proofs.M09.regularizedCoordinatePhase_connection_pairing B R s q v W
      (chartActionMetric_pos_of_target F T x hq)
    simp only [M08.spatialFDeriv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, smul_apply, smul_eq_mul, map_add, add_apply] at he ho
    change B (s, q) a W = B (s, q) alpha W
    dsimp only [B, R, alpha] at ho ⊢
    linarith
  calc
    a = M08.chartMetricDualInverse F T x (s, q) (B (s, q) a) :=
      (M08.chartMetricDualInverse_left F T x hq a).symm
    _ = alpha := by rw [hp, M08.chartMetricDualInverse_left F T x hq]




theorem closedChartEulerCurve_velocityPhase
    (hM04 : RicciFlowCurvatureTheory.{u}) {C : Set ℝ}
    (htime : ∀ r ∈ C, T - r ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C) (hnear : C ∈ 𝓝 s)
    (q : ℝ → EuclideanSpace ℝ (Fin n)) (hq : q s ∈ (extChartAt (𝓡 n) x).target)
    (heuler : ∀ W : EuclideanSpace ℝ (Fin n),
      M08.chartActionMetric F T x (s, q s)
          (derivWithin (derivWithin q C) C s +
            M08.closedChartConnection F T x C (s, q s) (derivWithin q C s) (derivWithin q C s)) W -
        M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
          (M08.chartActionPotential F T x) (s, q s) W +
        M08.timeWithinFDeriv C (extChartAt (𝓡 n) x).target
          (M08.chartActionMetric F T x) (s, q s) (derivWithin q C s) W = 0) :
    deriv (deriv q) s = (Proofs.M09.regularizedCoordinatePhase
      (M08.chartActionMetric F T x) (chartActionScalar F T x) (s, (q s, deriv q s))).2 := by
  have hv : derivWithin q C =ᶠ[𝓝 s] deriv q := by
    filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hnear)] with r hr
    exact derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hr)
  have ha : derivWithin (derivWithin q C) C s = deriv (deriv q) s := by
    rw [derivWithin_of_mem_nhds hnear]
    exact hv.deriv_eq
  have h := closedChartEulerPair_velocityPhase F T x hM04 htime hs hnear hq
    (derivWithin q C s) (derivWithin (derivWithin q C) C s) heuler
  rwa [ha, derivWithin_of_mem_nhds hnear] at h

end PoincareConjecture.M14
