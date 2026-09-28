import PoincareConjecture.Proofs.M14.Sec6_3_InteriorPotential
import PoincareConjecture.Proofs.M14.Mathlib.CoordinateJacobiLinearization

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)

theorem closedCoordinateJacobi_of_linearization
    (hM04 : RicciFlowCurvatureTheory.{u}) {C : Set ℝ} (hC : UniqueDiffOn ℝ C)
    (htime : ∀ r ∈ C, T - r ^ 2 ∈ J)
    (q Y : ℝ → EuclideanSpace ℝ (Fin n)) (hq : ContDiffOn ℝ ∞ q C)
    (hY : ContDiffOn ℝ ∞ Y C) (hmap : MapsTo q C (extChartAt (𝓡 n) x).target)
    {s : ℝ} (hs : s ∈ C) (hnear : C ∈ 𝓝 s)
    (hphase : deriv (deriv q) s = (Proofs.M09.regularizedCoordinatePhase
      (M08.chartActionMetric F T x) (chartActionScalar F T x) (s, (q s, deriv q s))).2)
    (hlinear : deriv (deriv Y) s =
      (fderiv ℝ (Proofs.M09.regularizedCoordinatePhase
        (M08.chartActionMetric F T x) (chartActionScalar F T x))
        (s, (q s, deriv q s)) (0, (Y s, deriv Y s))).2)
    (W : EuclideanSpace ℝ (Fin n)) :
    let A := derivWithin q C
    let d := fun r => derivWithin Y C r +
      M08.closedChartConnection F T x C (r, q r) (A r) (Y r)
    M08.chartActionMetric F T x (s, q s)
        (derivWithin d C s + M08.closedChartConnection F T x C (s, q s) (A s) (d s)) W -
      M08.closedChartJacobiPotential F T x C (s, q s) (A s) (Y s) W +
      M08.timeWithinFDeriv C (extChartAt (𝓡 n) x).target
        (M08.chartActionMetric F T x) (s, q s) (d s) W = 0 := by
  let B := M08.chartActionMetric F T x
  let R := chartActionScalar F T x
  let Γ := Proofs.M09.coordinateConnectionBilinear B
  let Ω := interior C ×ˢ (extChartAt (𝓡 n) x).target
  have hU := isOpen_extChartAt_target (I := 𝓡 n) x
  have hΩ : IsOpen Ω := isOpen_interior.prod hU
  have hsub : Ω ⊆ C ×ˢ (extChartAt (𝓡 n) x).target := prod_mono interior_subset Subset.rfl
  have hB : ContDiffOn ℝ ∞ B Ω :=
    (M08.chartActionMetric_closed_contDiffOn F T x htime).mono hsub
  have hR : ContDiffOn ℝ ∞ R Ω := (chartActionScalar_contDiffOn F T x hM04 htime).mono hsub
  have hsi : s ∈ interior C := mem_interior_iff_mem_nhds.mpr hnear
  have hqAt := hq.contDiffAt hnear
  have hYAt := hY.contDiffAt hnear
  have hq2At := ((hq.mono interior_subset).deriv_of_isOpen isOpen_interior
    (m := ∞) (by simp)).contDiffAt (isOpen_interior.mem_nhds hsi)
  have hY2At := ((hY.mono interior_subset).deriv_of_isOpen isOpen_interior
    (m := ∞) (by simp)).contDiffAt (isOpen_interior.mem_nhds hsi)
  have hj := coordinate_linearization_weightedJacobi B R Ω hΩ hB hR
    (fun _ hz => chartActionMetric_pos_of_target F T x hz.2)
    (fun _ hz => chartActionMetric_symm_of_target F T x hz.2) q Y s ⟨hsi, hmap hs⟩
    (hqAt.differentiableAt (by simp)) (hq2At.differentiableAt (by simp))
    (hYAt.differentiableAt (by simp)) (hY2At.differentiableAt (by simp)) hphase hlinear W
  let d := fun r => deriv Y r + Γ (r, q r) (deriv q r) (Y r)
  let f := fun r => derivWithin Y C r +
    M08.closedChartConnection F T x C (r, q r) (derivWithin q C r) (Y r)
  have hfd : f =ᶠ[𝓝 s] d := by
    filter_upwards [isOpen_interior.mem_nhds hsi,
      hqAt.continuousAt.preimage_mem_nhds (hU.mem_nhds (hmap hs))] with r hr hqr
    have hrC : C ∈ 𝓝 r := mem_interior_iff_mem_nhds.mp hr
    dsimp only [f, d, Γ, B]
    rw [derivWithin_of_mem_nhds hrC, derivWithin_of_mem_nhds hrC,
      closedChartConnection_eq_open F T x hrC hqr]
  have hdf : derivWithin f C s = deriv d s := by
    rw [derivWithin_of_mem_nhds hnear]
    exact hfd.deriv_eq
  change B (s, q s)
      (derivWithin f C s + M08.closedChartConnection F T x C (s, q s)
        (derivWithin q C s) (f s)) W -
    M08.closedChartJacobiPotential F T x C (s, q s) (derivWithin q C s) (Y s) W +
    M08.timeWithinFDeriv C (extChartAt (𝓡 n) x).target B (s, q s) (f s) W = 0
  rw [hdf, hfd.eq_of_nhds, derivWithin_of_mem_nhds hnear,
    closedChartConnection_eq_open F T x hnear (hmap hs),
    closedChartJacobiPotential_eq_open F T x hM04 hC htime hs hnear (hmap hs)]
  unfold M08.timeWithinFDeriv
  rw [fderivWithin_of_mem_nhds (prod_mem_nhds hnear (hU.mem_nhds (hmap hs)))]
  exact hj

end PoincareConjecture.M14
