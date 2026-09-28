import PoincareConjecture.Proofs.M09.SquareChartMetric
import PoincareConjecture.Proofs.M09.CoordinatePhase
import PoincareConjecture.Proofs.M09.TimeDependentFlow

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem exists_squareChart_local_flow {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (z0 : ℝ × (E × E))
    (hz0 : z0.1 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) ∧
      z0.2.1 ∈ (chartAt E p).target) :
    let S : Set (ℝ × (E × E)) :=
      {z | z.1 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) ∧ z.2.1 ∈ (chartAt E p).target}
    ∃ (beta : (ℝ × (E × E)) × ℝ → E × E) (W : Set (ℝ × (E × E))) (d : ℝ),
      IsOpen W ∧ z0 ∈ W ∧ W ⊆ S ∧ 0 < d ∧
      ContDiffOn ℝ ∞ beta (W ×ˢ Set.Ioo (-d) d) ∧
      (∀ z ∈ W, beta (z, 0) = z.2) ∧
      ∀ z ∈ W, ∀ t ∈ Set.Ioo (-d) d,
        (z.1 + t, beta (z, t)) ∈ S ∧
        HasDerivAt (fun r ↦ beta (z, r))
          (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
            (z.1 + t, beta (z, t))) t := by
  let U := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target
  let S : Set (ℝ × (E × E)) := {z | (z.1, z.2.1) ∈ U}
  have hU : IsOpen U := isOpen_Ioo.prod (chartAt E p).open_target
  have hS : IsOpen S :=
    hU.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hphase : ContDiffOn ℝ ∞
      (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)) S :=
    regularizedCoordinatePhase_smooth _ _ U hU
      (squareChartMetric_smooth F T b hb hwindow p)
      (squareChartScalar_smooth F hM04 T b hb hwindow p)
      (fun z hz v hv ↦ squareChartMetric_pos F T p z hz.2 v hv)
  exact exists_local_smooth_timeDependent_flow S hS _ hphase z0 hz0

end PoincareConjecture.Proofs.M09
