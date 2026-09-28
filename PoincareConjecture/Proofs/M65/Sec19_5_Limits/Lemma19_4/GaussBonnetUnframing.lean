import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetResidual
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetProjection

noncomputable section

set_option autoImplicit false

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

theorem compact_within_derivative_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℂ → E} {K U : Set ℂ} (hK : IsCompact K) (hKU : UniqueDiffOn ℝ K)
    (hU : IsOpen U) (hUK : U ⊆ K) (hq : ContDiffOn ℝ 1 q K) (v : ℂ) :
    MemLp (fun z => fderiv ℝ q z v) 2 (volume.restrict (K ∩ U)) := by
  have hd : ContinuousOn (fun z => fderivWithin ℝ q K z v) K :=
    (hq.continuousOn_fderivWithin hKU le_rfl).clm_apply continuousOn_const
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hd
  have hmeas : MeasurableSet (K ∩ U) := hK.measurableSet.inter hU.measurableSet
  let mu := volume.restrict (K ∩ U)
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono inter_subset_left) hK.measure_lt_top).ne
  have hmem : MemLp (fun z => fderivWithin ℝ q K z v) 2 mu :=
    MemLp.of_bound ((hd.mono inter_subset_left).aestronglyMeasurable hmeas) C
      ((ae_restrict_mem hmeas).mono fun z hz => hC z hz.1)
  apply hmem.ae_eq
  filter_upwards [ae_restrict_mem hmeas] with z hz
  rw [fderivWithin_of_mem_nhds (mem_of_superset (hU.mem_nhds hz.2) hUK)]

theorem inverse_frame_residual_derivative_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {L : ℂ → E →L[ℂ] E} {q : ℂ → E} {K U : Set ℂ}
    (hK : IsCompact K) (hKU : UniqueDiffOn ℝ K) (hU : IsOpen U) (hUK : U ⊆ K)
    (hL : ContDiffOn ℝ 1 L K) (hunit : ∀ z ∈ K, IsUnit (L z))
    (hq : ContinuousOn q K) (hq1 : ContDiffOn ℝ 1 q U) (v : ℂ)
    (hdq : MemLp (fun z => fderiv ℝ q z v) 2 (volume.restrict (K ∩ U))) :
    MemLp (fun z => fderiv ℝ (fun w => Ring.inverse (L w) (q w)) z v)
      2 (volume.restrict (K ∩ U)) := by
  let T := (E →L[ℂ] E) × E
  let p : ℂ → T := fun z => (L z, q z)
  let V : Set T := {w | IsUnit w.1}
  let H : T → E := fun w => Ring.inverse w.1 w.2
  have hV : IsOpen V := Units.isOpen.preimage continuous_fst
  have hInv : ContDiffOn ℝ 1 (fun w : T => Ring.inverse w.1) V := by
    intro w hw
    obtain ⟨u, hu⟩ := hw
    have hh : ContDiffAt ℝ 1 Ring.inverse w.1 := by
      simpa only [hu] using contDiffAt_ringInverse ℝ (n := 1) u
    exact (hh.comp w contDiffAt_fst).contDiffWithinAt
  have hH : ContDiffOn ℝ 1 H V := by
    let R := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
    exact (R.contDiff.comp_contDiffOn hInv).clm_apply contDiffOn_snd
  have hL1 : ContDiffOn ℝ 1 L U := hL.mono hUK
  have hp : ContinuousOn p K := hL.continuousOn.prodMk hq
  have hp1 : ContDiffOn ℝ 1 p U := hL1.prodMk hq1
  have hdp : MemLp (fun z => fderiv ℝ p z v) 2 (volume.restrict (K ∩ U)) := by
    have hm : MemLp (fun z => (fderiv ℝ L z v, fderiv ℝ q z v)) 2
        (volume.restrict (K ∩ U)) :=
      memLp_prod_iff.mpr ⟨compact_within_derivative_memLp hK hKU hU hUK hL v, hdq⟩
    apply hm.ae_eq
    filter_upwards [ae_restrict_mem (hK.measurableSet.inter hU.measurableSet)] with z hz
    have hD := ((hL1.contDiffAt (hU.mem_nhds hz.2)).differentiableAt
      one_ne_zero).hasFDerivAt.prodMk
        ((hq1.contDiffAt (hU.mem_nhds hz.2)).differentiableAt one_ne_zero).hasFDerivAt
    exact (congrArg (fun D : ℂ →L[ℝ] T => D v) hD.fderiv).symm
  exact actual_comp_derivative_memLp hK hU hV hp hp1 (fun z hz => hunit z hz) hH v hdp

end PoincareConjecture.M65Branch
