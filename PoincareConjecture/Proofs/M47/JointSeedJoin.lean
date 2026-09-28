import PoincareConjecture.Proofs.M47.JointSeedSquarePath
import PoincareConjecture.Proofs.M09.SmoothJoinDensityBound
import PoincareConjecture.Proofs.M09.JoinIntegralEstimate











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J}




theorem exists_jointSeed_smooth_join
    (hM04 : RicciFlowCurvatureTheory.{u}) (T d b0 c : ℝ) (hd : 0 < d)
    (hwindow : Icc (T - d) T ⊆ J) (hc : 0 < c) (hcb : c < b0)
    (hb : b0 < Real.sqrt d) (alpha beta : ℝ → M) {Da Db : Set ℝ}
    (hDa : IsOpen Da) (hDb : IsOpen Db) (hIa : Icc 0 b0 ⊆ Da)
    (hIb : Icc 0 (Real.sqrt d) ⊆ Db)
    (halpha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha Da)
    (hbeta : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ beta Db)
    (heq : alpha c = beta c) (error : ℝ) (herror : 0 < error) :
    ∃ path : BackwardTimePath F T 0 d,
      path.curve 0 = alpha 0 ∧ path.curve d = beta (Real.sqrt d) ∧
      backwardLLength F T 0 d path.curve ≤
        (∫ s in 0..c, Proofs.M09.squareCurveActionDensity F T alpha s) +
          (∫ s in c..Real.sqrt d, Proofs.M09.squareCurveActionDensity F T beta s) + error := by
  let U := (Da ∩ Db) ∩ Ioo (-Real.sqrt d) (Real.sqrt d)
  have hU : IsOpen U := (hDa.inter hDb).inter isOpen_Ioo
  have hbpos : 0 < b0 := hc.trans hcb
  have hIU : Icc 0 b0 ⊆ U := by
    intro s hs
    exact ⟨⟨hIa hs, hIb ⟨hs.1, hs.2.trans hb.le⟩⟩,
      (neg_lt_zero.mpr (Real.sqrt_pos.mpr hd)).trans_le hs.1, hs.2.trans_lt hb⟩
  have halphaU := halpha.mono (show U ⊆ Da from fun _ hs => hs.1.1)
  have hbetaU := hbeta.mono (show U ⊆ Db from fun _ hs => hs.1.2)
  obtain ⟨r, hr, hrc, hcr, B, hB, hjoin⟩ := Proofs.M09.exists_smoothJoin_uniform_density
    F hM04 T d hd hwindow alpha beta U hU halphaU hbetaU inter_subset_right
      b0 c hIU ⟨hc, hcb⟩ heq
  let w := min (r / 2) (error / (8 * (B + 1)))
  have hw : 0 < w := lt_min (by positivity) (by positivity)
  have hwr : w < r := (min_le_left _ _).trans_lt (by linarith)
  have hbudget : 4 * B * w ≤ error := by
    have hden : 0 < 8 * (B + 1) := by positivity
    have hsmall : w * (8 * (B + 1)) ≤ error := (le_div_iff₀ hden).1 (min_le_right _ _)
    nlinarith [mul_nonneg hB hw.le]
  obtain ⟨gamma, hgamma, hleft, hright, hbound⟩ := hjoin w hw hwr
  let V := U ∪ (Db ∩ Ioi (c + w))
  have hV : IsOpen V := hU.union (hDb.inter isOpen_Ioi)
  have hIV : Icc 0 (Real.sqrt d) ⊆ V := by
    intro s hs
    by_cases hsb : s ≤ b0
    · exact Or.inl (hIU ⟨hs.1, hsb⟩)
    · refine Or.inr ⟨hIb hs, ?_⟩
      change c + w < s
      linarith [lt_of_not_ge hsb]
  have hgammaV : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ gamma V := by
    intro s hs
    rcases hs with hs | hs
    · exact (hgamma.contMDiffAt (hU.mem_nhds hs)).contMDiffWithinAt
    · have hagree : gamma =ᶠ[𝓝 s] beta := by
        filter_upwards [Ioi_mem_nhds hs.2] with z hz
        exact hright (show z ∈ Ici (c + w) by
          change c + w ≤ z
          exact (show c + w < z from hz).le)
      exact ((hbeta.contMDiffAt (hDb.mem_nhds hs.1)).congr_of_eventuallyEq
        hagree).contMDiffWithinAt
  obtain ⟨path, hpath, haction⟩ := exists_jointSeed_closed_square_path
    (F := F) hM04 T d hd hwindow gamma hV hIV hgammaV
  let f : ℝ → ℝ := fun s => Proofs.M09.squareCurveActionDensity F T alpha (min s b0)
  have hbase : ContinuousOn (Proofs.M09.squareCurveActionDensity F T alpha) (Icc 0 b0) :=
    (Proofs.M09.squareCurveActionDensity_contDiffOn F hM04 T d hd hwindow
      alpha U hU halphaU inter_subset_right).continuousOn.mono hIU
  have hclip : MapsTo (fun s : ℝ => min s b0) (Icc 0 (Real.sqrt d)) (Icc 0 b0) :=
    fun s hs => ⟨le_min hs.1 hbpos.le, min_le_right _ _⟩
  have hfi : IntervalIntegrable f volume 0 (Real.sqrt d) :=
    (hbase.comp ((continuous_id.min continuous_const).continuousOn) hclip).intervalIntegrable_of_Icc
      (Real.sqrt_nonneg d)
  have hbi := jointSeed_square_density_integrable
    (F := F) hM04 T d hd hwindow beta hDb hIb hbeta
  have hgi := jointSeed_square_density_integrable
    (F := F) hM04 T d hd hwindow gamma hV hIV hgammaV
  have hleftDensity : EqOn (Proofs.M09.squareCurveActionDensity F T gamma) f (Ioo 0 (c - w)) := by
    intro s hs
    have hagree : gamma =ᶠ[𝓝 s] alpha := by
      filter_upwards [Iio_mem_nhds hs.2] with z hz
      exact hleft (show z ∈ Iic (c - w) by
        change z ≤ c - w
        exact (show z < c - w from hz).le)
    rw [Proofs.M09.squareCurveActionDensity_congr F T gamma alpha s hagree]
    dsimp [f]
    rw [min_eq_left (by linarith [hs.2] : s ≤ b0)]
  have hrightDensity : EqOn (Proofs.M09.squareCurveActionDensity F T gamma)
      (Proofs.M09.squareCurveActionDensity F T beta) (Ioo (c + w) (Real.sqrt d)) := by
    intro s hs
    apply Proofs.M09.squareCurveActionDensity_congr
    filter_upwards [Ioi_mem_nhds hs.1] with z hz
    exact hright (show z ∈ Ici (c + w) by
      change c + w ≤ z
      exact (show c + w < z from hz).le)
  have hband : ∀ s ∈ Icc (c - w) (c + w), |f s| ≤ B ∧
      |Proofs.M09.squareCurveActionDensity F T beta s| ≤ B ∧
      |Proofs.M09.squareCurveActionDensity F T gamma s| ≤ B := by
    intro s hs
    dsimp [f]
    rw [min_eq_left (by linarith [hs.2] : s ≤ b0)]
    exact hbound s hs
  have hestimate := Proofs.M09.integral_join_error_bound f
    (Proofs.M09.squareCurveActionDensity F T beta)
    (Proofs.M09.squareCurveActionDensity F T gamma) 0 (Real.sqrt d) c w B hw
    (by linarith) (by linarith) hfi hbi hgi hleftDensity hrightDensity hband
  have hleftIntegral : (∫ s in 0..c, f s) =
      ∫ s in 0..c, Proofs.M09.squareCurveActionDensity F T alpha s := by
    apply intervalIntegral.integral_congr_Ioo_of_le hc.le
    intro s hs
    dsimp [f]
    rw [min_eq_left (hs.2.le.trans hcb.le)]
  rw [hleftIntegral] at hestimate
  refine ⟨path, ?_, ?_, ?_⟩
  · simp only [hpath, Real.sqrt_zero]
    exact hleft (show (0 : ℝ) ∈ Iic (c - w) by change 0 ≤ c - w; linarith)
  · rw [hpath]
    exact hright (show Real.sqrt d ∈ Ici (c + w) by change c + w ≤ Real.sqrt d; linarith)
  · rw [haction]
    have hdiff := (le_abs_self ((∫ s in 0..Real.sqrt d,
      Proofs.M09.squareCurveActionDensity F T gamma s) -
      ((∫ s in 0..c, Proofs.M09.squareCurveActionDensity F T alpha s) +
        ∫ s in c..Real.sqrt d, Proofs.M09.squareCurveActionDensity F T beta s))).trans
        (hestimate.trans hbudget)
    linarith

end PoincareConjecture.M47
