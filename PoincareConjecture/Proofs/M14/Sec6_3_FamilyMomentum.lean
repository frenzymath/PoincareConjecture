import PoincareConjecture.Proofs.M14.Mathlib.ClosedFamilyTimeDerivative
import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerMomentum

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {J C : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x₀ : M)
  {U : Set E} (hU : IsOpen U) (hC : UniqueDiffOn ℝ C)
  (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
  (q : E × ℝ → EuclideanSpace ℝ (Fin n)) (hq : ContDiffOn ℝ ∞ q (U ×ˢ C))
  (hmap : MapsTo q (U ×ˢ C) (extChartAt (𝓡 n) x₀).target)

include hU hC htime hq hmap

theorem closedChartFamily_phase_contDiffOn :
    ContDiffOn ℝ ∞ (fun z => (q z,
      M08.chartMomentumVector (M08.chartActionMetric F T x₀ (z.2, q z))
        (derivWithin (fun s => q (z.1, s)) C z.2))) (U ×ˢ C) := by
  have hv := closedFamily_timeDerivative_contDiffOn hU hC q hq
  have hB := (M08.chartActionMetric_closed_contDiffOn F T x₀ htime).comp
    (contDiffOn_snd.prodMk hq) (fun z hz => ⟨hz.2, hmap hz⟩)
  let L := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv
  exact hq.prodMk (L.contDiff.comp_contDiffOn (hB.clm_apply hv))

theorem closedChartFamily_initialPhase_contDiffOn {r : ℝ} (hr : r ∈ C) :
    ContDiffOn ℝ ∞ (fun z => (q (z, r),
      M08.chartMomentumVector (M08.chartActionMetric F T x₀ (r, q (z, r)))
        (derivWithin (fun s => q (z, s)) C r))) U :=
  (closedChartFamily_phase_contDiffOn F T x₀ hU hC htime q hq hmap).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, hr⟩)

end PoincareConjecture.M14
