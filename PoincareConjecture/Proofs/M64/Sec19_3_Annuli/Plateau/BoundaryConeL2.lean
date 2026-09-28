import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeFields














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal InnerProductSpace

namespace PoincareConjecture.M64BoundaryCone

open M65Interior

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem cone_field_norm_le
    (g : C → E)
    (r : ℝ) (v0 : C)
    (v d : ℝ → C) (s θ : ℝ) (i : Fin 2) {K ρ : ℝ}
    (hK : 0 ≤ K) (hg : ‖fderiv ℝ g (coneCoordinates r v0 v s θ)‖ ≤ K)
    (h0 : ‖v0‖ ≤ ρ) (hv : ‖v θ‖ ≤ ρ) :
    ‖coneCartesianField g r v0 v d s θ i‖ ≤ |r⁻¹| * K * (2 * ρ + ‖d θ‖) := by
  let A := fderiv ℝ g (coneCoordinates r v0 v s θ)
  have he : |Proofs.M58.angularPoint θ i| ≤ 1 := by
    fin_cases i
    · exact Real.abs_cos_le_one θ
    · exact Real.abs_sin_le_one θ
  have hτ : |Proofs.M58.angularVector θ i| ≤ 1 := by
    fin_cases i
    · change |-Real.sin θ| ≤ 1
      simpa only [abs_neg] using Real.abs_sin_le_one θ
    · exact Real.abs_cos_le_one θ
  have hA (z : C) : ‖A z‖ ≤ K * ‖z‖ :=
    (A.le_opNorm z).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg z))
  have hsub : ‖v θ - v0‖ ≤ 2 * ρ := by
    exact (norm_sub_le _ _).trans (by linarith)
  change ‖r⁻¹ • (Proofs.M58.angularPoint θ i • A (v θ - v0) +
    Proofs.M58.angularVector θ i • A (d θ))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |r⁻¹| * (‖Proofs.M58.angularPoint θ i • A (v θ - v0)‖ +
        ‖Proofs.M58.angularVector θ i • A (d θ)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)
    _ ≤ |r⁻¹| * (‖A (v θ - v0)‖ + ‖A (d θ)‖) := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_of_le_one_left (norm_nonneg _) he)
          (mul_le_of_le_one_left (norm_nonneg _) hτ)) (abs_nonneg _)
    _ ≤ |r⁻¹| * (K * (2 * ρ) + K * ‖d θ‖) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact add_le_add ((hA _).trans (mul_le_mul_of_nonneg_left hsub hK)) (hA _)
    _ = _ := by ring




theorem cone_reconstruction_continuous
    {g : C → E}
    {v : ℝ → C} {v0 : C}
    {r ρ a b : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hv : ContinuousOn v (Icc a b))
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ) (hvb : MapsTo v (Icc a b) (closedBall 0 ρ)) :
    ContinuousOn (fun p : ℝ × ℝ => g (coneCoordinates r v0 v p.1 p.2))
        (Icc 0 r ×ˢ Icc a b) ∧
      ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ g (coneCoordinates r v0 v p.1 p.2))
        (Icc 0 r ×ˢ Icc a b) := by
  have hvp : ContinuousOn (fun p : ℝ × ℝ => v p.2) (Icc 0 r ×ˢ Icc a b) :=
    hv.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hc : ContinuousOn (fun p : ℝ × ℝ => coneCoordinates r v0 v p.1 p.2)
      (Icc 0 r ×ˢ Icc a b) :=
    continuousOn_const.add ((continuous_fst.continuousOn.div_const r).smul
      (hvp.sub continuousOn_const))
  have hmaps : MapsTo (fun p : ℝ × ℝ => coneCoordinates r v0 v p.1 p.2)
      (Icc 0 r ×ˢ Icc a b) (ball 0 (2 * ρ)) := by
    intro p hp
    exact (closedBall_subset_ball (by linarith))
      (coneCoordinates_mem_closedBall hr h0 (hvb hp.2) hp.1)
  exact ⟨hg.continuousOn.comp hc hmaps,
    (hg.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).comp hc hmaps⟩




theorem coneCartesianField_memLp
    {g : C → E}
    {v d : ℝ → C} {v0 : C}
    {r ρ a b K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : ContinuousOn v (Icc a b))
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ) (hvb : MapsTo v (Icc a b) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (hD : ∀ y ∈ closedBall (0 : C) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (i : Fin 2) :
    MemLp (fun p : ℝ × ℝ => coneCartesianField g r v0 v d p.1 p.2 i) 2
      (volume.restrict (Icc 0 r ×ˢ Icc a b)) := by
  let S : Set (ℝ × ℝ) := Icc 0 r ×ˢ Icc a b
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  let : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hvp : ContinuousOn (fun p : ℝ × ℝ => v p.2 - v0) S :=
    (hv.comp continuous_snd.continuousOn (fun _ hp => hp.2)).sub continuousOn_const
  have hA : AEStronglyMeasurable
      (fun p : ℝ × ℝ => fderiv ℝ g (coneCoordinates r v0 v p.1 p.2))
      (volume.restrict S) :=
    (cone_reconstruction_continuous hr hρ hv hg h0 hvb).2.aestronglyMeasurable hS
  have hdp : MemLp (fun p : ℝ × ℝ => d p.2) 2 (volume.restrict S) := by
    have h := hd.comp_snd (volume.restrict (Icc (0 : ℝ) r))
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  have happly : Continuous (fun q :
      (C →L[ℝ] E) ×
        C => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  have hrad := happly.comp_aestronglyMeasurable (hA.prodMk (hvp.aestronglyMeasurable hS))
  have hang := happly.comp_aestronglyMeasurable (hA.prodMk hdp.1)
  have he : Continuous (fun p : ℝ × ℝ => Proofs.M58.angularPoint p.2 i) := by
    fin_cases i
    · exact Real.continuous_cos.comp continuous_snd
    · exact Real.continuous_sin.comp continuous_snd
  have hτ : Continuous (fun p : ℝ × ℝ => Proofs.M58.angularVector p.2 i) := by
    fin_cases i
    · exact (Real.continuous_sin.comp continuous_snd).neg
    · exact Real.continuous_cos.comp continuous_snd
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => coneCartesianField g r v0 v d p.1 p.2 i) (volume.restrict S) :=
    ((he.aestronglyMeasurable.smul hrad).add
      (hτ.aestronglyMeasurable.smul hang)).const_smul r⁻¹
  have hmajor : MemLp (fun p : ℝ × ℝ => |r⁻¹| * K * (2 * ρ + ‖d p.2‖)) 2
      (volume.restrict S) :=
    ((memLp_const (2 * ρ)).add hdp.norm).const_mul (|r⁻¹| * K)
  apply hmajor.mono' hm
  filter_upwards [ae_restrict_mem hS] with p hp
  exact cone_field_norm_le g r v0 v d p.1 p.2 i hK
    (hD _ (coneCoordinates_mem_closedBall hr h0 (hvb hp.2) hp.1))
    (mem_closedBall_zero_iff.mp h0) (mem_closedBall_zero_iff.mp (hvb hp.2))

end PoincareConjecture.M64BoundaryCone
