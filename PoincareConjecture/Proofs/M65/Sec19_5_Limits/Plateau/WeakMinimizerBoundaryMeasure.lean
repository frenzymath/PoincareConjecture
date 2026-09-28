import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerLocalization
import PoincareConjecture.Proofs.M03.Existence.ChartLpNative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Topology.TietzeExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology SchwartzMap ContDiff InnerProductSpace

namespace PoincareConjecture

noncomputable def m65CircleBoundaryMeasure : Measure LoopPlane :=
  (volume.restrict (Icc (-Real.pi) Real.pi)).map Proofs.M58.angularPoint

noncomputable def m65CircleBoundaryPullback :
    Lp ℝ 2 m65CircleBoundaryMeasure →ₗᵢ[ℝ]
      Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi)) :=
  ChartLpNative.mapPullbackL2 Proofs.M58.angularPoint
    Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable

theorem m65CircleBoundaryPullback_coe (b : Lp ℝ 2 m65CircleBoundaryMeasure) :
    m65CircleBoundaryPullback b =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => b (Proofs.M58.angularPoint t) :=
  ChartLpNative.mapPullbackL2_coe _ _ b

theorem m65CircleBoundaryPullback_closed : IsClosed (range m65CircleBoundaryPullback) :=
  m65CircleBoundaryPullback.isometry.isClosedEmbedding.isClosed_range

theorem m65CircleBoundary_continuous_class (b : C(LoopCircle, ℝ)) :
    ∃ B : Lp ℝ 2 m65CircleBoundaryMeasure,
      m65CircleBoundaryPullback B =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
        fun t => b ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩ := by
  have hs : IsClosed {z : LoopPlane | ‖z‖ = 1} :=
    isClosed_eq continuous_norm continuous_const
  obtain ⟨F, hF⟩ := ContinuousMap.exists_extension' hs.isClosedEmbedding_subtypeVal b
  have hA := Proofs.M58.contDiff_angularPoint.continuous
  have hfL2 : MemLp (fun t => F (Proofs.M58.angularPoint t)) 2
      (volume.restrict (Icc (-Real.pi) Real.pi)) := by
    exact (memLp_two_iff_integrable_sq (F.continuous.comp hA).aestronglyMeasurable).mpr
      (((F.continuous.comp hA).pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have hFL2 : MemLp F 2 m65CircleBoundaryMeasure :=
    (memLp_map_measure_iff F.continuous.aestronglyMeasurable hA.measurable.aemeasurable).mpr
      hfL2
  refine ⟨hFL2.toLp F, ?_⟩
  apply (m65CircleBoundaryPullback_coe _).trans
  have hae := ae_of_ae_map hA.measurable.aemeasurable hFL2.coeFn_toLp
  filter_upwards [hae] with t ht
  rw [ht]
  exact congrFun hF ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩

private theorem m65CircleBoundary_norm_ae :
    ∀ᵐ z ∂m65CircleBoundaryMeasure, ‖z‖ = 1 := by
  apply (ae_map_iff
    Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
  exact ae_of_all _ Proofs.M58.norm_angularPoint

private theorem m65CircleBoundary_pairing (b : Lp ℝ 2 m65CircleBoundaryMeasure)
    (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) :
    (∫ t in Icc (-Real.pi) Real.pi,
      m65CircleBoundaryPullback b t * m65DiskBoundaryTest test i t) =
        ∫ z, b z * (test z * z i) ∂m65CircleBoundaryMeasure := by
  have hm : AEStronglyMeasurable (fun z : LoopPlane => b z * (test z * z i))
      m65CircleBoundaryMeasure :=
    (Lp.memLp b).1.mul
      ((test.continuous.mul (EuclideanSpace.proj i).continuous).aestronglyMeasurable)
  calc
    _ = ∫ t in Icc (-Real.pi) Real.pi, b (Proofs.M58.angularPoint t) *
        (test (Proofs.M58.angularPoint t) * Proofs.M58.angularPoint t i) := by
      apply integral_congr_ae
      filter_upwards [m65CircleBoundaryPullback_coe b] with t ht
      simp only [ht, m65DiskBoundaryTest]
    _ = _ := (integral_map
      Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable hm).symm

theorem m65CircleBoundary_trace_unique
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b c : Lp ℝ 2 m65CircleBoundaryMeasure}
    (hb : M65DiskWeakTrace u d (m65CircleBoundaryPullback b))
    (hc : M65DiskWeakTrace u d (m65CircleBoundaryPullback c)) : b = c := by
  let : IsFiniteMeasure m65CircleBoundaryMeasure := by
    unfold m65CircleBoundaryMeasure
    infer_instance
  have hi : Integrable (fun z => b z - c z) m65CircleBoundaryMeasure :=
    (MemLp.integrable (by norm_num) (Lp.memLp b)).sub
      (MemLp.integrable (by norm_num) (Lp.memLp c))
  have hzero : ∀ᵐ z ∂m65CircleBoundaryMeasure, b z - c z = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hi.locallyIntegrable
    intro g hg hgs
    let φ := hgs.toSchwartzMap hg
    let ψ (i : Fin 2) := SchwartzMap.smulLeftCLM ℝ (EuclideanSpace.proj i) φ
    have hψ (i : Fin 2) (z : LoopPlane) : ψ i z = z i * g z := by
      simp only [ψ, SchwartzMap.smulLeftCLM_apply_apply
        (EuclideanSpace.proj i).hasTemperateGrowth, smul_eq_mul]
      rfl
    have htest (i : Fin 2) : MemLp (fun z : LoopPlane => ψ i z * z i) 2
        m65CircleBoundaryMeasure := by
      apply MemLp.of_bound
        (((ψ i).continuous.mul (EuclideanSpace.proj i).continuous).aestronglyMeasurable)
        (SchwartzMap.seminorm ℝ 0 0 (ψ i))
      filter_upwards [m65CircleBoundary_norm_ae] with z hz
      change ‖ψ i z * z i‖ ≤ _
      rw [norm_mul]
      calc
        _ ≤ ‖ψ i z‖ * 1 := mul_le_mul_of_nonneg_left
          ((PiLp.norm_apply_le z i).trans_eq hz) (norm_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact (ψ i).norm_le_seminorm ℝ z
    have hpair (i : Fin 2) :
        (∫ z, (b z - c z) * (ψ i z * z i) ∂m65CircleBoundaryMeasure) = 0 := by
      have h1 := m65WeakTrace_green_integral hb (ψ i) i
      have h2 := m65WeakTrace_green_integral hc (ψ i) i
      rw [m65CircleBoundary_pairing] at h1 h2
      have hib := (Lp.memLp b).integrable_mul (htest i)
      have hic := (Lp.memLp c).integrable_mul (htest i)
      change Integrable (fun z => b z * (ψ i z * z i)) m65CircleBoundaryMeasure at hib
      change Integrable (fun z => c z * (ψ i z * z i)) m65CircleBoundaryMeasure at hic
      simp_rw [sub_mul]
      rw [integral_sub hib hic, sub_eq_zero]
      exact h1.symm.trans h2
    have htestI (i : Fin 2) : Integrable
        (fun z => (b z - c z) * (ψ i z * z i)) m65CircleBoundaryMeasure := by
      exact ((Lp.memLp b).sub (Lp.memLp c)).integrable_mul (htest i)
    have hsum := congrArg (fun k : Fin 2 → ℝ => ∑ i, k i) (funext hpair)
    simp only [Finset.sum_const_zero] at hsum
    rw [← integral_finsetSum _ fun i _ => htestI i] at hsum
    apply Eq.trans _ hsum
    apply integral_congr_ae
    filter_upwards [m65CircleBoundary_norm_ae] with z hz
    have hs : ∑ i : Fin 2, (z i) ^ 2 = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, hz, one_pow]
    simp only [hψ, Fin.sum_univ_two, smul_eq_mul] at hs ⊢
    linear_combination -(g z * (b z - c z)) * hs
  apply Lp.ext
  exact hzero.mono fun _ hz => sub_eq_zero.mp hz

end PoincareConjecture
