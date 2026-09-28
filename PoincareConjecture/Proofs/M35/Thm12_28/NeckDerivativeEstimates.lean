import PoincareConjecture.Proofs.M35.Thm12_28.NeckBall
import PoincareConjecture.Proofs.M35.Thm12_28.NeckBackwardCurvature
import PoincareConjecture.Proofs.M35.RawFlow.MetricSpace
import PoincareConjecture.Proofs.M09.RiemannianProper
import PoincareConjecture.Statements.Ch04.CurvatureTheory










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35




theorem exists_short_neck_derivative_bounds (P : RicciFlowCurvatureTheory.{0}) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
        ∀ T : ℝ, 1 / 2 ≤ T → T ≤ 1 →
        ∀ (F : RicciFlow 3 StandardCapSpace (Icc 0 T)) (x : StandardCapSpace)
          (N : StandardCylinderPatch epsilon⁻¹ x), MetricComplete (F.metric 0) →
          (∀ s ∈ Icc (0 : ℝ) T,
            RoundCylinderClose epsilon (s - T) (roundCylinderPullback (F.metric s) N.coordinate)) →
          (F.connection T).curvatureDerivativeNorm k x ≤ C := by
  obtain ⟨delta, hdelta, hbound⟩ := exists_backward_neck_carrier_curvature_bound
  refine ⟨min delta (1 / 24), lt_min hdelta (by norm_num), fun k => ?_⟩
  obtain ⟨C, hC, hShi⟩ := P.local_derivative_estimates 3 k 2 2 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hpower : 0 < (1 / 2 : ℝ) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C / (1 / 2 : ℝ) ^ ((k : ℝ) / 2), div_pos hC hpower,
    fun epsilon he hedelta T hTlower hTupper F x N hcomplete hclose => ?_⟩
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hTlower
  have hesmall : epsilon ≤ 1 / 24 := hedelta.trans (min_le_right _ _)
  have hecurv : epsilon ≤ delta := hedelta.trans (min_le_left _ _)
  have hball : (F.metric 0).ball x (1 / 2) ⊆ N.carrier :=
    N.center_ball_subset_carrier (F.metric 0) he hesmall
      ⟨by linarith, by linarith⟩ (hclose 0 ⟨le_rfl, hT.le⟩)
  have hcurv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T)
      (y : StandardCapSpace) (hy : y ∈ (F.metric 0).ball x (1 / 2)) :
      (F.connection s).curvatureTensorNorm y ≤ 2 :=
    (hbound epsilon he hecurv (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩
      (F.metric s) (F.connection s) x N (hclose s hs) y (hball hy)).le
  have hcompact : IsCompact (closure ((F.metric 0).ball x (1 / 2))) :=
    Proofs.M09.isCompact_closure_metric_ball (F.metric 0) hcomplete x (1 / 2)
  have hx : x ∈ (F.metric 0).ball x ((1 / 2) / 2) := by
    change (F.metric 0).edist x x < ENNReal.ofReal ((1 / 2) / 2)
    rw [← RiemannianMetric.toEMetricSpace_edist]
    have hz := @edist_self StandardCapSpace
      (F.metric 0).toEMetricSpace.toPseudoEMetricSpace x
    rw [hz]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have h := hShi StandardCapSpace T hT (by norm_num; exact hTupper) F x
    hcompact hcurv T ⟨hT, le_rfl⟩ x hx
  apply h.trans
  exact div_le_div_of_nonneg_left hC.le hpower
    (Real.rpow_le_rpow (by norm_num) hTlower (by positivity))




theorem exists_unit_neck_derivative_bounds (P : RicciFlowCurvatureTheory.{0}) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
        ∀ (F : RicciFlow 3 StandardCapSpace (Icc 0 1)) (x : StandardCapSpace)
          (N : StandardCylinderPatch epsilon⁻¹ x), MetricComplete (F.metric 0) →
          (∀ s ∈ Icc (0 : ℝ) 1,
            RoundCylinderClose epsilon (s - 1) (roundCylinderPullback (F.metric s) N.coordinate)) →
          (F.connection 1).curvatureDerivativeNorm k x ≤ C := by
  obtain ⟨delta, hdelta, hbounds⟩ := exists_short_neck_derivative_bounds P
  refine ⟨delta, hdelta, fun k => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hbounds k
  exact ⟨C, hC, fun epsilon he hedelta => hbound epsilon he hedelta 1 (by norm_num) le_rfl⟩

end PoincareConjecture.M35
