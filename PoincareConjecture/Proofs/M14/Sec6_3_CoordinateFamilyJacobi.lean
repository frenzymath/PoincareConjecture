import PoincareConjecture.Proofs.M14.Sec6_3_InteriorJacobi
import PoincareConjecture.Proofs.M14.Mathlib.ParameterPhaseLinearization
import PoincareConjecture.Proofs.M14.Mathlib.ClosedParameterDerivative










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (p : M)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem closedCoordinateJacobi_of_parameterFamily
    (hM04 : RicciFlowCurvatureTheory.{u}) {C : Set ℝ} (hC : UniqueDiffOn ℝ C)
    (htime : ∀ r ∈ C, T - r ^ 2 ∈ J) {U : Set E} (hU : IsOpen U)
    (f : ℝ × E → EuclideanSpace ℝ (Fin n))
    (hf : ContDiffOn ℝ ∞ f (C ×ˢ U))
    (hmap : ∀ r ∈ C, ∀ y ∈ U, f (r, y) ∈ (extChartAt (𝓡 n) p).target)
    {s : ℝ} (hs : s ∈ C) (hnear : C ∈ 𝓝 s) {x : E} (hx : x ∈ U) (v : E)
    (hode : ∀ y ∈ U, HasDerivAt
      (fun r => (f (r, y), deriv (fun t => f (t, y)) r))
      (Proofs.M09.regularizedCoordinatePhase
        (M08.chartActionMetric F T p) (chartActionScalar F T p)
        (s, (f (s, y), deriv (fun t => f (t, y)) s))) s)
    (W : EuclideanSpace ℝ (Fin n)) :
    let q : ℝ → EuclideanSpace ℝ (Fin n) := fun r => f (r, x)
    let Y : ℝ → EuclideanSpace ℝ (Fin n) := fun r => fderiv ℝ (fun y => f (r, y)) x v
    let A := derivWithin q C
    let d := fun r => derivWithin Y C r +
      M08.closedChartConnection F T p C (r, q r) (A r) (Y r)
    M08.chartActionMetric F T p (s, q s)
        (derivWithin d C s + M08.closedChartConnection F T p C (s, q s) (A s) (d s)) W -
      M08.closedChartJacobiPotential F T p C (s, q s) (A s) (Y s) W +
      M08.timeWithinFDeriv C (extChartAt (𝓡 n) p).target
        (M08.chartActionMetric F T p) (s, q s) (d s) W = 0 := by
  let B := Proofs.M09.regularizedCoordinatePhase
    (M08.chartActionMetric F T p) (chartActionScalar F T p)
  let q : ℝ → EuclideanSpace ℝ (Fin n) := fun r => f (r, x)
  let Y : ℝ → EuclideanSpace ℝ (Fin n) := fun r => fderiv ℝ (fun y => f (r, y)) x v
  let Ω := interior C ×ˢ (extChartAt (𝓡 n) p).target
  have hΩ : IsOpen Ω := isOpen_interior.prod (isOpen_extChartAt_target (I := 𝓡 n) p)
  have hsub : Ω ⊆ C ×ˢ (extChartAt (𝓡 n) p).target :=
    prod_mono interior_subset Subset.rfl
  have hB : ContDiffAt ℝ ∞ B (s, (q s, deriv q s)) :=
    (Proofs.M09.regularizedCoordinatePhase_smooth
      (M08.chartActionMetric F T p) (chartActionScalar F T p) Ω hΩ
      ((M08.chartActionMetric_closed_contDiffOn F T p htime).mono hsub)
      ((chartActionScalar_contDiffOn F T p hM04 htime).mono hsub)
      (fun _ hz => chartActionMetric_pos_of_target F T p hz.2)).contDiffAt
        ((hΩ.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mem_nhds
          ⟨mem_interior_iff_mem_nhds.mpr hnear, hmap s hs x hx⟩)
  have hlinear := parameterDifferential_secondOrderLinearization isOpen_interior hU f
    (hf.mono (prod_mono interior_subset Subset.rfl)) B
    (mem_interior_iff_mem_nhds.mpr hnear) hx v
    (hB.differentiableAt (by simp)) hode
  have hphase : deriv (deriv q) s = (B (s, (q s, deriv q s))).2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, ContinuousLinearMap.coe_snd'] using
      ((hode x hx).hasFDerivAt.snd).hasDerivAt.deriv
  have hq : ContDiffOn ℝ ∞ q C := hf.comp
    (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hr => ⟨hr, hx⟩)
  have hY : ContDiffOn ℝ ∞ Y C := parameterDerivative_contDiffOn hC hU f hf hx v
  exact closedCoordinateJacobi_of_linearization F T p hM04 hC htime q Y hq hY
    (fun r hr => hmap r hr x hx) hs hnear hphase hlinear W

end PoincareConjecture.M14
