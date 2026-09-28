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

theorem exists_squareChart_initial_flow {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (y0 v0 : E) (hy0 : y0 ∈ (chartAt E p).target) :
    ∃ (beta : (E × E) × ℝ → E × E) (W : Set (E × E)) (d : ℝ),
      IsOpen W ∧ (y0, v0) ∈ W ∧ W ⊆ (chartAt E p).target ×ˢ Set.univ ∧ 0 < d ∧
      ContDiffOn ℝ ∞ beta (W ×ˢ Set.Ioo (-d) d) ∧
      (∀ q ∈ W, beta (q, 0) = q) ∧
      ∀ q ∈ W, ∀ s ∈ Set.Ioo (-d) d,
        s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) ∧ (beta (q, s)).1 ∈ (chartAt E p).target ∧
        HasDerivAt (fun r ↦ beta (q, r))
          (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
            (s, beta (q, s))) s := by
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
  have hzero : (0 : ℝ) ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) :=
    ⟨neg_lt_zero.mpr (Real.sqrt_pos.mpr hb), Real.sqrt_pos.mpr hb⟩
  obtain ⟨B, V, d, hV, h0V, hVS, hd, hB, hB0, hBode⟩ :=
    exists_local_smooth_timeDependent_flow S hS _ hphase (0, (y0, v0)) ⟨hzero, hy0⟩
  let W : Set (E × E) := {q | (0, q) ∈ V}
  let beta : (E × E) × ℝ → E × E := fun z ↦ B ((0, z.1), z.2)
  have hW : IsOpen W := hV.preimage (continuous_const.prodMk continuous_id)
  have hmap : ContDiff ℝ ∞ (fun z : (E × E) × ℝ ↦ (((0 : ℝ), z.1), z.2)) :=
    (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd
  refine ⟨beta, W, d, hW, h0V, ?_, hd, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨(hVS hq).2, Set.mem_univ _⟩
  · exact hB.comp hmap.contDiffOn (fun z hz ↦ ⟨hz.1, hz.2⟩)
  · intro q hq
    exact hB0 (0, q) hq
  · intro q hq s hs
    have h := hBode (0, q) hq s hs
    have ht : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) := by
      simpa only [zero_add] using h.1.1
    have hy : (beta (q, s)).1 ∈ (chartAt E p).target := h.1.2
    refine ⟨ht, hy, ?_⟩
    simpa only [zero_add] using h.2

end PoincareConjecture.Proofs.M09
