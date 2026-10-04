import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Euler.InteriorConnection

/-!
# The actual scalar potential in the open coordinate linearization

Morgan-Tian equation (6.2), Lemma 6.10 and Lemma 6.19,
pp. 106, 109-110, 114. The actual potential is 2s^2 times the
actual scalar curvature. Its spatial derivatives and the genuine
closed connection identify the corrected open Jacobi potential.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)

/-- The actual scalar curvature in the same extended chart as M08's
action metric, the scalar term of equation (6.2), p. 106. -/
noncomputable def chartActionScalar (z : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  (F.connection (T - z.1 ^ 2)).scalarCurvature ((extChartAt (𝓡 n) x).symm z.2)

/-- The actual scalar coordinate is smooth on every admissible closed
time-chart product, the coefficient regularity in Lemmas 6.10 and
6.19, pp. 109-110, 114. -/
theorem chartActionScalar_contDiffOn
    (hM04 : RicciFlowCurvatureTheory.{u}) {C : Set ℝ}
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞ (chartActionScalar F T x) (C ×ˢ (extChartAt (𝓡 n) x).target) := by
  have ht : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => T - z.1 ^ 2)
      (C ×ˢ (extChartAt (𝓡 n) x).target) :=
    (contDiff_const.sub (contDiff_fst.pow 2)).contMDiff.contMDiffOn
  have hq : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓡 n) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (extChartAt (𝓡 n) x).symm z.2)
      (C ×ˢ (extChartAt (𝓡 n) x).target) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp
      contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2)
  exact ((hM04.scalar_regular n M J F).comp (ht.prodMk hq)
    (fun z hz => ⟨htime z.1 hz.1, mem_univ _⟩)).contDiffOn

/-- At an interior time, the first spatial derivative of the actual
potential is 2s^2 times the actual scalar spatial derivative,
equation (6.2), p. 106, and Lemma 6.10, pp. 109-110. -/
theorem chartActionPotential_spatialWithin_eq
    (hM04 : RicciFlowCurvatureTheory.{u}) {C : Set ℝ}
    (htime : ∀ r ∈ C, T - r ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C) (hnear : C ∈ 𝓝 s)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target) :
    M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
      (M08.chartActionPotential F T x) (s, q) =
      (2 * s ^ 2) • M08.spatialFDeriv (chartActionScalar F T x) (s, q) := by
  have hU := isOpen_extChartAt_target (I := 𝓡 n) x
  have hR := M08.hasFDerivAt_spatialWithin hU (chartActionScalar F T x)
    (chartActionScalar_contDiffOn F T x hM04 htime) hs hq
  have hP := M08.hasFDerivAt_spatialWithin hU (M08.chartActionPotential F T x)
    (M08.chartActionPotential_closed_contDiffOn F hM04 T x htime) hs hq
  have hscaled : HasFDerivAt (fun y => M08.chartActionPotential F T x (s, y))
      ((2 * s ^ 2) • M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
        (chartActionScalar F T x) (s, q)) q := hR.const_smul (2 * s ^ 2)
  rw [hP.unique hscaled, M08.spatialWithinFDeriv_eq_spatialFDeriv hU _ hnear hq]

/-- The second spatial derivative retains the same factor 2s^2 and
the actual derivative of the scalar spatial differential, as used
in the Hessian term of Lemma 6.10, pp. 109-110. -/
theorem chartActionPotential_spatialWithin_twice_eq
    (hM04 : RicciFlowCurvatureTheory.{u}) {C : Set ℝ} (hC : UniqueDiffOn ℝ C)
    (htime : ∀ r ∈ C, T - r ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C) (hnear : C ∈ 𝓝 s)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target) :
    M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
      (M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
        (M08.chartActionPotential F T x)) (s, q) =
      (2 * s ^ 2) • fderiv ℝ (fun y => M08.spatialFDeriv (chartActionScalar F T x) (s, y)) q := by
  have hU := isOpen_extChartAt_target (I := 𝓡 n) x
  have hR := (chartActionScalar_contDiffOn F T x hM04 htime).contDiffAt
    (prod_mem_nhds hnear (hU.mem_nhds hq))
  have hD : ContDiffAt ℝ ∞
      (fun y => M08.spatialFDeriv (chartActionScalar F T x) (s, y)) q :=
    ((hR.fderiv_right (m := ∞) (by simp)).comp q
      (contDiffAt_const.prodMk contDiffAt_id)).clm_comp contDiffAt_const
  have hP := M08.hasFDerivAt_spatialWithin hU
    (M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (M08.chartActionPotential F T x))
    (M08.spatialWithinFDeriv_contDiffOn hC hU _
      (M08.chartActionPotential_closed_contDiffOn F hM04 T x htime)) hs hq
  have heq : (fun y => M08.spatialWithinFDeriv C (extChartAt (𝓡 n) x).target
      (M08.chartActionPotential F T x) (s, y)) =ᶠ[𝓝 q]
      fun y => (2 * s ^ 2) • M08.spatialFDeriv (chartActionScalar F T x) (s, y) := by
    filter_upwards [hU.mem_nhds hq] with y hy
    exact chartActionPotential_spatialWithin_eq F T x hM04 htime hs hnear hy
  exact hP.unique (((hD.differentiableAt (by simp)).hasFDerivAt.const_smul
    (2 * s ^ 2)).congr_of_eventuallyEq heq)

/-- The frozen closed Jacobi potential is exactly the open-coordinate
potential of the actual metric and scalar term at every interior
time-chart point, Lemmas 6.10 and 6.19, pp. 109-110, 114. -/
theorem closedChartJacobiPotential_eq_open
    (hM04 : RicciFlowCurvatureTheory.{u}) {C : Set ℝ} (hC : UniqueDiffOn ℝ C)
    (htime : ∀ r ∈ C, T - r ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C) (hnear : C ∈ 𝓝 s)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target)
    (A : EuclideanSpace ℝ (Fin n)) :
    let Γ := Proofs.M09.coordinateConnectionBilinear (M08.chartActionMetric F T x)
    let P := fun y => M08.spatialFDeriv (chartActionScalar F T x) (s, y)
    M08.closedChartJacobiPotential F T x C (s, q) A =
      M08.weightedChartPotential (M08.chartActionMetric F T x (s, q)) (Γ (s, q))
        ((fderiv ℝ Γ (s, q)).comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n))))
        (fderiv ℝ Γ (s, q) (1, 0)) ((2 * s ^ 2) • P q)
        ((2 * s ^ 2) • fderiv ℝ P q) A := by
  dsimp only
  unfold M08.closedChartJacobiPotential
  rw [closedChartConnection_eq_open F T x hnear hq,
    chartActionPotential_spatialWithin_eq F T x hM04 htime hs hnear hq,
    chartActionPotential_spatialWithin_twice_eq F T x hM04 hC htime hs hnear hq]
  unfold M08.spatialWithinFDeriv M08.timeWithinFDeriv
  rw [closedChartConnection_fderivWithin_eq_open F T x hnear hq]

end PoincareMT.M14
