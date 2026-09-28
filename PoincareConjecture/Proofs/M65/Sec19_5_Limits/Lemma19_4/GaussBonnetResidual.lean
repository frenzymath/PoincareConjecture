import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetGauge
import Mathlib.MeasureTheory.SpecificCodomains.Pi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

theorem cauchyGauge_derivatives_memLp {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {R B0 : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2)
    (hU : IsOpen U) (hAC1 : ContDiffOn ℝ 1 A U) :
    MemLp (fun z => fderiv ℝ (cauchyGauge A) z 1) 2 (volume.restrict U) ∧
      MemLp (fun z => fderiv ℝ (cauchyGauge A) z I) 2 (volume.restrict U) := by
  let E := Fin n → ℂ
  let T : (E →L[ℂ] E) ≃L[ℂ] (Fin n → E) := ContinuousLinearEquiv.piRing (Fin n)
  have hP := (cauchyGauge_contDiffOn_of_C1_coefficient
    hR hB hA hs hb hsmall hU hAC1).1
  have hpart (v : ℂ) (hv : v = 1 ∨ v = I) :
      MemLp (fun z => fderiv ℝ (cauchyGauge A) z v) 2 (volume.restrict U) := by
    have ht : MemLp (fun z => T (fderiv ℝ (cauchyGauge A) z v)) 2 (volume.restrict U) := by
      apply memLp_pi_iff.mpr
      intro j
      apply memLp_pi_iff.mpr
      intro i
      let L : (E →L[ℂ] E) →L[ℂ] ℂ :=
        (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.apply ℂ E (Pi.single j 1))
      have hh := cauchyGauge_projection_derivatives_memLp
        hR hB hA hs hb hsmall hU hAC1 L
      have hvh : MemLp (fun z => fderiv ℝ (fun w => L (cauchyGauge A w)) z v)
          2 (volume.restrict U) := hv.elim (fun h => h ▸ hh.1) (fun h => h ▸ hh.2)
      apply hvh.ae_eq
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      have hd := (L.restrictScalars ℝ).hasFDerivAt.comp z
        ((hP.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero).hasFDerivAt
      change HasFDerivAt (fun w => L (cauchyGauge A w)) _ z at hd
      rw [hd.fderiv]
      rfl
    have hh := T.symm.toContinuousLinearMap.comp_memLp' ht
    exact hh.ae_eq (ae_of_all _ fun z => T.symm_apply_apply _)
  exact ⟨hpart 1 (Or.inl rfl), hpart I (Or.inr rfl)⟩

theorem cauchyGauge_residual_derivatives_memLp {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {R B0 : ℝ} {U V K : Set ℂ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2)
    (hU : IsOpen U) (hAC1 : ContDiffOn ℝ 1 A U)
    {u : ℂ → Fin n → ℂ} (hV : IsOpen V) (hu : ContDiffOn ℝ 1 u V)
    (hK : IsCompact K) (hKV : K ⊆ V) :
    MemLp (fun z => fderiv ℝ (fun w => cauchyGauge A w (u w)) z 1)
      2 (volume.restrict (K ∩ U)) ∧
    MemLp (fun z => fderiv ℝ (fun w => cauchyGauge A w (u w)) z I)
      2 (volume.restrict (K ∩ U)) := by
  let E := Fin n → ℂ
  let P := cauchyGauge A
  let mu := volume.restrict (K ∩ U)
  have hKU : MeasurableSet (K ∩ U) := hK.measurableSet.inter hU.measurableSet
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono inter_subset_left) hK.measure_lt_top).ne
  have hP := (cauchyGauge_contDiffOn_of_C1_coefficient
    hR hB hA hs hb hsmall hU hAC1).1
  have hPs := cauchyGauge_measurable_spec hR hB hA hs hb hsmall
  have hPb (z : ℂ) : ‖P z‖ ≤ 2 := by
    have hh := norm_le_norm_sub_add (P z) (1 : E →L[ℂ] E)
    rw [norm_one] at hh
    linarith [hPs.2.2.1 z]
  have hDP := cauchyGauge_derivatives_memLp hR hB hA hs hb hsmall hU hAC1
  have huK := hu.continuousOn.mono hKV
  have hum : AEStronglyMeasurable u mu :=
    (huK.mono inter_subset_left).aestronglyMeasurable hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn huK
  have hpart (v : ℂ) (hv : v = 1 ∨ v = I) :
      MemLp (fun z => fderiv ℝ (fun w => P w (u w)) z v) 2 mu := by
    have hdP : MemLp (fun z => fderiv ℝ P z v) 2 mu := by
      apply MemLp.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
      exact hv.elim (fun h => h ▸ hDP.1) (fun h => h ▸ hDP.2)
    have huD : ContinuousOn (fun z => fderiv ℝ u z v) K :=
      ((hu.fderiv_of_isOpen (m := 0) hV (by norm_num)).continuousOn.clm_apply
        continuousOn_const).mono hKV
    obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn huD
    have hdu : MemLp (fun z => fderiv ℝ u z v) 2 mu :=
      MemLp.of_bound ((huD.mono inter_subset_left).aestronglyMeasurable hKU) C1
        ((ae_restrict_mem hKU).mono fun z hz => hC1 z hz.1)
    have hfirst : MemLp (fun z => P z (fderiv ℝ u z v)) 2 mu := by
      apply hdu.of_le_mul (c := 2)
      · exact (ContinuousLinearMap.id ℂ (E →L[ℂ] E)).aestronglyMeasurable_comp₂
          hPs.1.aestronglyMeasurable hdu.1
      · filter_upwards [] with z
        exact ((P z).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hPb z) (norm_nonneg _))
    have hsecond : MemLp (fun z => fderiv ℝ P z v (u z)) 2 mu := by
      apply hdP.of_le_mul (c := C)
      · exact (ContinuousLinearMap.id ℂ (E →L[ℂ] E)).aestronglyMeasurable_comp₂ hdP.1 hum
      · filter_upwards [ae_restrict_mem hKU] with z hz
        exact ((fderiv ℝ P z v).le_opNorm _).trans
          ((mul_le_mul_of_nonneg_left (hC z hz.1) (norm_nonneg _)).trans_eq (mul_comm _ _))
    apply (hfirst.add hsecond).ae_eq
    filter_upwards [ae_restrict_mem hKU] with z hz
    have hp := (hP.contDiffAt (hU.mem_nhds hz.2)).differentiableAt one_ne_zero
    have huz := (hu.contDiffAt (hV.mem_nhds (hKV hz.1))).differentiableAt one_ne_zero
    let L := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
    have hR := L.hasFDerivAt.comp z hp.hasFDerivAt
    have hD := hR.clm_apply huz.hasFDerivAt
    exact (congrArg (fun D : ℂ →L[ℝ] E => D v) hD.fderiv).symm
  exact ⟨hpart 1 (Or.inl rfl), hpart I (Or.inr rfl)⟩

theorem cauchyGauge_analytic_residual_local_memLp {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {R B0 : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2)
    (hAC1 : ContDiffOn ℝ 1 A (ball (0 : ℂ) R ∩ {z | z.im ≠ 0}))
    {u : ℂ → Fin n → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      ContinuousOn (fun z => cauchyGauge A z (u z)) (closedBall (0 : ℂ) r) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, cauchyGauge A z (u z) ≠ 0) ∧
      MemLp (fun z => fderiv ℝ (fun w => cauchyGauge A w (u w)) z 1)
        2 (volume.restrict (closedBall (0 : ℂ) r ∩ {z | z.im ≠ 0})) ∧
      MemLp (fun z => fderiv ℝ (fun w => cauchyGauge A w (u w)) z I)
        2 (volume.restrict (closedBall (0 : ℂ) r ∩ {z | z.im ≠ 0})) := by
  have hP := cauchyGauge_measurable_spec hR hB hA hs hb hsmall
  have hQ0 : cauchyGauge A 0 (u 0) ≠ 0 := by
    intro h
    apply hu0
    have hh := congrArg
      (fun v => (Ring.inverse (cauchyGauge A 0) :
        (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) v) h
    change (Ring.inverse (cauchyGauge A 0) * cauchyGauge A 0) (u 0) = _ at hh
    rw [Ring.inverse_mul_cancel _ (hP.2.2.2 0)] at hh
    simpa using hh
  have hQc : ContinuousAt (fun z => cauchyGauge A z (u z)) 0 :=
    hP.1.continuousAt.clm_apply hu.continuousAt
  have hnear := hu.eventually_analyticAt.and (hQc.eventually_ne hQ0)
  obtain ⟨s, hs0, hsnear⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min s R / 2
  have hr : 0 < r := half_pos (lt_min hs0 hR)
  have hrs : r < s := (half_lt_self (lt_min hs0 hR)).trans_le (min_le_left s R)
  have hrR : r < R := (half_lt_self (lt_min hs0 hR)).trans_le (min_le_right s R)
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) s :=
    closedBall_subset_ball hrs
  have huC : ContDiffOn ℝ 1 u (ball (0 : ℂ) s) := fun z hz =>
    (((hsnear hz).1.contDiffAt : ContDiffAt ℂ 1 u z).restrict_scalars ℝ).contDiffWithinAt
  have hU : IsOpen (ball (0 : ℂ) R ∩ {z : ℂ | z.im ≠ 0}) :=
    isOpen_ball.inter (isOpen_ne_fun continuous_im continuous_const)
  have hmem := cauchyGauge_residual_derivatives_memLp hR hB hA hs hb hsmall
    hU hAC1 isOpen_ball huC (isCompact_closedBall (0 : ℂ) r) hsub
  have hset : closedBall (0 : ℂ) r ∩ (ball (0 : ℂ) R ∩ {z : ℂ | z.im ≠ 0}) =
      closedBall (0 : ℂ) r ∩ {z : ℂ | z.im ≠ 0} := by
    ext z
    exact ⟨fun hz => ⟨hz.1, hz.2.2⟩,
      fun hz => ⟨hz.1, closedBall_subset_ball hrR hz.1, hz.2⟩⟩
  refine ⟨r, hr, hrR,
    hP.1.continuousOn.clm_apply (huC.continuousOn.mono hsub),
    fun z hz => (hsnear (hsub hz)).2, ?_⟩
  simpa only [hset] using hmem

end PoincareConjecture.M65Branch
