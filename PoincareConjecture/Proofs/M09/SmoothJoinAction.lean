import PoincareConjecture.Proofs.M09.SmoothJoinDensityBound
import PoincareConjecture.Proofs.M09.JoinIntegralEstimate

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem squareCurveActionDensity_intervalIntegrable {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (α : ℝ → M) (D : Set ℝ) (hD : IsOpen D) (hI : Set.Icc 0 (Real.sqrt b) ⊆ D)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D) :
    IntervalIntegrable (squareCurveActionDensity F T α) MeasureTheory.volume 0 (Real.sqrt b) := by
  let U := D ∩ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)
  have hU : IsOpen U := hD.inter isOpen_Ioo
  have hIU : Set.Icc 0 (Real.sqrt b) ⊆ U := by
    intro s hs
    exact ⟨hI hs, (neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  exact ((squareCurveActionDensity_contDiffOn F hM04 T τmax hτmax hwindow α U hU
    (hα.mono Set.inter_subset_left) Set.inter_subset_right).continuousOn.mono hIU).intervalIntegrable_of_Icc
      (Real.sqrt_nonneg b)

theorem exists_backwardPath_smoothJoin_action_le {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (α β : ℝ → M) (D : Set ℝ) (hD : IsOpen D) (hI : Set.Icc 0 (Real.sqrt b) ⊆ D)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β D)
    (c : ℝ) (hc : c ∈ Set.Ioo 0 (Real.sqrt b)) (heq : α c = β c)
    (η : ℝ) (hη : 0 < η) :
    ∃ P : BackwardTimePath F T 0 b, P.curve 0 = α 0 ∧ P.curve b = β (Real.sqrt b) ∧
      backwardLLength F T 0 b P.curve ≤
        (∫ s in 0..c, squareCurveActionDensity F T α s) +
          (∫ s in c..Real.sqrt b, squareCurveActionDensity F T β s) + η := by
  let U := D ∩ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)
  have hU : IsOpen U := hD.inter isOpen_Ioo
  have hIU : Set.Icc 0 (Real.sqrt b) ⊆ U := by
    intro s hs
    exact ⟨hI hs, (neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hαU := hα.mono (show U ⊆ D from Set.inter_subset_left)
  have hβU := hβ.mono (show U ⊆ D from Set.inter_subset_left)
  obtain ⟨r, hr, hrc, hcr, C, hC, hjoin⟩ := exists_smoothJoin_uniform_density
    F hM04 T τmax hτmax hwindow α β U hU hαU hβU Set.inter_subset_right
      (Real.sqrt b) c hIU hc heq
  let d := min (r / 2) (η / (8 * (C + 1)))
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdr : d < r := (min_le_left _ _).trans_lt (by linarith)
  have herror : 4 * C * d ≤ η := by
    have hden : 0 < 8 * (C + 1) := by positivity
    have hsmall : d * (8 * (C + 1)) ≤ η :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith [mul_nonneg hC hd.le]
  obtain ⟨γ, hγ, hleft, hright, hbound⟩ := hjoin d hd hdr
  obtain ⟨P, hP, hPaction⟩ := exists_backwardPath_of_smoothSquareCurve F hM04 T τmax
    hτmax hwindow b hb hmax γ U hU hIU hγ
  have hiα := squareCurveActionDensity_intervalIntegrable F hM04 T τmax hτmax hwindow
    b hb hmax α U hU hIU hαU
  have hiβ := squareCurveActionDensity_intervalIntegrable F hM04 T τmax hτmax hwindow
    b hb hmax β U hU hIU hβU
  have hiγ := squareCurveActionDensity_intervalIntegrable F hM04 T τmax hτmax hwindow
    b hb hmax γ U hU hIU hγ
  have hdleft : Set.EqOn (squareCurveActionDensity F T γ) (squareCurveActionDensity F T α)
      (Set.Ioo 0 (c - d)) := by
    intro s hs
    apply squareCurveActionDensity_congr
    filter_upwards [gt_mem_nhds hs.2] with t ht
    exact hleft ht.le
  have hdright : Set.EqOn (squareCurveActionDensity F T γ) (squareCurveActionDensity F T β)
      (Set.Ioo (c + d) (Real.sqrt b)) := by
    intro s hs
    apply squareCurveActionDensity_congr
    filter_upwards [lt_mem_nhds hs.1] with t ht
    exact hright ht.le
  have hestimate := integral_join_error_bound (squareCurveActionDensity F T α)
    (squareCurveActionDensity F T β) (squareCurveActionDensity F T γ)
    0 (Real.sqrt b) c d C hd (by linarith) (by linarith) hiα hiβ hiγ hdleft hdright hbound
  refine ⟨P, ?_, ?_, ?_⟩
  · simp only [hP, Real.sqrt_zero]
    exact hleft (by change (0 : ℝ) ≤ c - d; linarith)
  · rw [hP]
    exact hright (by change c + d ≤ Real.sqrt b; linarith)
  · change backwardLLength F T 0 b P.curve ≤ _
    rw [hPaction]
    change (∫ s in 0..Real.sqrt b, squareCurveActionDensity F T γ s) ≤ _
    have hle := (le_abs_self ((∫ s in 0..Real.sqrt b, squareCurveActionDensity F T γ s) -
      ((∫ s in 0..c, squareCurveActionDensity F T α s) +
        ∫ s in c..Real.sqrt b, squareCurveActionDensity F T β s))).trans hestimate
    linarith

end PoincareConjecture.Proofs.M09
