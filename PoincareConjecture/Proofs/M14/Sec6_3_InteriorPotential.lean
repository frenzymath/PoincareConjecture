import PoincareConjecture.Proofs.M14.Sec6_3_InteriorConnection

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)

noncomputable def chartActionScalar (z : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  (F.connection (T - z.1 ^ 2)).scalarCurvature ((extChartAt (𝓡 n) x).symm z.2)

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

end PoincareConjecture.M14
