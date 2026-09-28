import PoincareConjecture.Proofs.M35.Uniqueness.CompleteDistanceSupports
import PoincareConjecture.Proofs.M04.ShiCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_raw_distance_square_compact_exhaustion
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T : ℝ} (hT : 0 ≤ T) (hTlt : T < G.lifetime)
    (p x₀ : StandardCapSpace) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : Set StandardCapSpace, IsCompact C ∧ x₀ ∈ C ∧
      ∀ t ∈ Icc 0 T, ∀ x ∉ interior C, A ≤ rawDistanceSquare G p t x := by
  obtain ⟨K, hK, hbound⟩ := G.curvature_locally_bounded T hT hTlt
  have hRm (t : ℝ) (ht : t ∈ Icc 0 T) (x : StandardCapSpace) :
      (G.flow.connection t).curvatureTensorNorm x ≤ K :=
    (le_abs_self _).trans (hbound t ht x)
  let a := Real.exp (3 * K * T)
  have ha : 0 < a := Real.exp_pos _
  let d₀ := ((G.flow.metric 0).edist p x₀).toReal
  have hd₀ : 0 ≤ d₀ := ENNReal.toReal_nonneg
  let R := a * (A + 1) + d₀ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let C := closure ((G.flow.metric 0).ball p R)
  have hcompact : IsCompact C := Proofs.M09.isCompact_closure_metric_ball
    (G.flow.metric 0) (G.complete P ⟨le_rfl, hT.trans_lt hTlt⟩) p R
  have hx₀ball : x₀ ∈ (G.flow.metric 0).ball p R := by
    change (G.flow.metric 0).edist p x₀ < ENNReal.ofReal R
    rw [← ENNReal.ofReal_toReal ((G.flow.metric 0).edist_ne_top p x₀)]
    apply (ENNReal.ofReal_lt_ofReal_iff hR).mpr
    change d₀ < R
    have hprod : 0 < a * (A + 1) := mul_pos ha (by linarith)
    dsimp [R]
    linarith
  refine ⟨C, hcompact, subset_closure hx₀ball, ?_⟩
  intro t ht x hx
  have hxball : x ∉ (G.flow.metric 0).ball p R := fun hh =>
    hx ((M04.initial_ball_isOpen (G.flow.metric 0) p R).subset_interior_closure hh)
  have hd : R ≤ ((G.flow.metric 0).edist p x).toReal := by
    have hh := ENNReal.toReal_mono ((G.flow.metric 0).edist_ne_top p x)
      (le_of_not_gt hxball)
    simpa only [ENNReal.toReal_ofReal hR.le] using hh
  have hcompare := raw_distance_comparison_of_curvature_bound G hTlt hK hRm
    ⟨le_rfl, hT⟩ ht ht.1 p x
  have he : Real.exp (3 * K * (t - 0)) ≤ a := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using ht.2)
      (by positivity : 0 ≤ 3 * K)
  have hcompare' : ((G.flow.metric 0).edist p x).toReal ≤
      a * ((G.flow.metric t).edist p x).toReal :=
    hcompare.trans (mul_le_mul_of_nonneg_right he ENNReal.toReal_nonneg)
  have hAxd : A + 1 ≤ ((G.flow.metric t).edist p x).toReal := by
    apply le_of_mul_le_mul_left (a := a) _ ha
    have hAR : a * (A + 1) ≤ R := by dsimp [R]; linarith
    exact hAR.trans (hd.trans hcompare')
  change A ≤ 1 + ((G.flow.metric t).edist p x).toReal ^ 2
  nlinarith [sq_nonneg (((G.flow.metric t).edist p x).toReal - 1)]

end PoincareConjecture.M35.Uniqueness
