import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryGraph
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter Metric Complex
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture





theorem m65SmoothDisk_map_bound (φ ψ : LoopPlane → LoopPlane)
    (hφ : ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 φ z)
    (hψ : ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 ψ z)
    (hφdisk : MapsTo φ loopDiskSet loopDiskSet)
    (hψdisk : MapsTo ψ loopDiskSet loopDiskSet)
    (hleft : ∀ z ∈ loopDiskSet, ψ (φ z) = z)
    (hright : ∀ z ∈ loopDiskSet, φ (ψ z) = z) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (volume.restrict loopDiskSet).map φ ≤ C • volume.restrict loopDiskSet := by
  have hs : MeasurableSet loopDiskSet := isClosed_closedBall.measurableSet
  have hmeas : AEMeasurable φ (volume.restrict loopDiskSet) :=
    (show ContinuousOn φ loopDiskSet from
      fun z hz => (hφ z hz).continuousAt.continuousWithinAt).aemeasurable hs
  have hJ : ContinuousOn (fun z => |(fderiv ℝ ψ z).det|) loopDiskSet := by
    intro z hz
    exact ((ContinuousLinearMap.continuous_det.continuousAt.comp
      ((hψ z hz).continuousAt_fderiv one_ne_zero)).abs).continuousWithinAt
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : LoopPlane) 1).bddAbove_image hJ
  refine ⟨ENNReal.ofReal K, ENNReal.ofReal_ne_top, Measure.le_iff.mpr ?_⟩
  intro A hA
  have heq : φ ⁻¹' A ∩ loopDiskSet = ψ '' (A ∩ loopDiskSet) := by
    ext z
    constructor
    · rintro ⟨hzA, hz⟩
      exact ⟨φ z, ⟨hzA, hφdisk hz⟩, hleft z hz⟩
    · rintro ⟨w, ⟨hwA, hw⟩, rfl⟩
      exact ⟨by change φ (ψ w) ∈ A; rwa [hright w hw], hψdisk hw⟩
  rw [Measure.map_apply_of_aemeasurable hmeas hA, Measure.restrict_apply' hs, heq,
    Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  calc
    _ ≤ ∫⁻ z in A ∩ loopDiskSet, ENNReal.ofReal |(fderiv ℝ ψ z).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv volume (hA.inter hs)
        (fun z hz => ((hψ z hz.2).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt)
    _ ≤ ∫⁻ _z in A ∩ loopDiskSet, ENNReal.ofReal K := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hA.inter hs)] with z hz
      exact ENNReal.ofReal_le_ofReal (hK ⟨z, hz.2, rfl⟩)
    _ = _ := by simp

private theorem m65Angular_lipschitz : LipschitzWith 1 Proofs.M58.angularPoint := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (Proofs.M58.hasDerivAt_angularPoint t).differentiableAt)
  intro t
  rw [(Proofs.M58.hasDerivAt_angularPoint t).deriv]
  change ‖Proofs.M58.angularVector t‖₊ ≤ 1
  apply NNReal.coe_le_coe.mp
  change ‖Proofs.M58.angularVector t‖ ≤ (1 : ℝ)
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Proofs.M58.angularVector, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]

private theorem m65Angular_inverse_bound {s t : ℝ} (hst : |s - t| ≤ Real.pi) :
    dist s t ≤ Real.pi * dist (Proofs.M58.angularPoint s) (Proofs.M58.angularPoint t) := by
  have heq : ‖Proofs.M58.angularPoint s - Proofs.M58.angularPoint t‖ ^ 2 =
      2 - 2 * Real.cos (s - t) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two, Proofs.M58.angularPoint, PiLp.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq s, Real.sin_sq_add_cos_sq t]
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one_sub_mul_cos_sq hst)
    (sq_nonneg Real.pi)
  have hp := Real.pi_pos
  have hpne := ne_of_gt hp
  field_simp at hc
  rw [Real.dist_eq, dist_eq_norm]
  have hn := norm_nonneg (Proofs.M58.angularPoint s - Proofs.M58.angularPoint t)
  have ha := abs_nonneg (s - t)
  have hasq := sq_abs (s - t)
  apply (sq_le_sq₀ ha (mul_nonneg hp.le hn)).mp
  have heq' := congrArg (fun x : ℝ => Real.pi ^ 2 * x) heq
  nlinarith

private theorem m65Angular_half_measure_le (a b : ℝ) (hab : b - a ≤ Real.pi)
    (A : Set LoopPlane) :
    volume (Proofs.M58.angularPoint ⁻¹' A ∩ Icc a b) ≤
      ENNReal.ofReal Real.pi * (μH[1] : Measure LoopPlane) A := by
  let S := Icc a b
  let T : Set S := {t | Proofs.M58.angularPoint t ∈ A}
  have hanti : AntilipschitzWith ⟨Real.pi, Real.pi_pos.le⟩
      (fun t : S => Proofs.M58.angularPoint t) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro s t
    exact m65Angular_inverse_bound (abs_le.mpr
      ⟨by linarith [s.property.1, t.property.2],
        by linarith [s.property.2, t.property.1]⟩)
  have himage : ((↑) : S → ℝ) '' T = Proofs.M58.angularPoint ⁻¹' A ∩ Icc a b := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs, s.property⟩
    · rintro ⟨htA, ht⟩
      exact ⟨⟨t, ht⟩, htA, rfl⟩
  have hiso := (isometry_subtype_coe (s := S)).hausdorffMeasure_image
    (d := 1) (Or.inl zero_le_one) T
  have hh := hanti.le_hausdorffMeasure_image (d := 1) zero_le_one T
  rw [← hiso, himage, hausdorffMeasure_real] at hh
  simp only [ENNReal.rpow_one] at hh
  rw [ENNReal.ofReal_eq_coe_nnreal Real.pi_pos.le]
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ bot_le
  apply measure_mono
  rintro _ ⟨t, ht, rfl⟩
  exact ht

private theorem m65Angular_principal {z : LoopPlane} (hz : ‖z‖ = 1) :
    Proofs.M58.angularPoint (Complex.arg (orthonormalBasisOneI.repr.symm z)) = z := by
  let w := orthonormalBasisOneI.repr.symm z
  have hw : ‖w‖ = 1 := (orthonormalBasisOneI.repr.symm.norm_map z).trans hz
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  change Proofs.M58.angularPoint (Complex.arg w) = z
  ext i
  fin_cases i
  · change Real.cos (Complex.arg w) = z 0
    rw [Complex.cos_arg hwne, hw, div_one]
    simp [w, orthonormalBasisOneI_repr_symm_apply]
  · change Real.sin (Complex.arg w) = z 1
    rw [Complex.sin_arg, hw, div_one]
    simp [w, orthonormalBasisOneI_repr_symm_apply]

private theorem m65Boundary_hausdorff_lower (A : Set LoopPlane) (hA : MeasurableSet A) :
    (μH[1] : Measure LoopPlane) (A ∩ {z | ‖z‖ = 1}) ≤ m65CircleBoundaryMeasure A := by
  let S := Proofs.M58.angularPoint ⁻¹' A ∩ Icc (-Real.pi) Real.pi
  have himage : Proofs.M58.angularPoint '' S = A ∩ {z : LoopPlane | ‖z‖ = 1} := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht.1, Proofs.M58.norm_angularPoint t⟩
    · rintro ⟨hzA, hz⟩
      refine ⟨Complex.arg (orthonormalBasisOneI.repr.symm z), ?_, m65Angular_principal hz⟩
      exact ⟨by change Proofs.M58.angularPoint _ ∈ A; rwa [m65Angular_principal hz],
        (Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hh := m65Angular_lipschitz.hausdorffMeasure_image_le (d := 1) zero_le_one S
  rw [himage, hausdorffMeasure_real] at hh
  simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at hh
  unfold m65CircleBoundaryMeasure
  rw [Measure.map_apply Proofs.M58.contDiff_angularPoint.continuous.measurable hA,
    Measure.restrict_apply' measurableSet_Icc]
  exact hh

private theorem m65Boundary_hausdorff_upper (A : Set LoopPlane) (hA : MeasurableSet A) :
    m65CircleBoundaryMeasure A ≤
      ENNReal.ofReal (2 * Real.pi) * (μH[1] : Measure LoopPlane) (A ∩ {z | ‖z‖ = 1}) := by
  let B := A ∩ {z : LoopPlane | ‖z‖ = 1}
  have hBpre : Proofs.M58.angularPoint ⁻¹' A = Proofs.M58.angularPoint ⁻¹' B := by
    ext t
    simp only [mem_preimage, B, mem_inter_iff, mem_ofPred_eq, Proofs.M58.norm_angularPoint,
      and_true]
  have hsplit : Proofs.M58.angularPoint ⁻¹' B ∩ Icc (-Real.pi) Real.pi =
      (Proofs.M58.angularPoint ⁻¹' B ∩ Icc (-Real.pi) 0) ∪
        (Proofs.M58.angularPoint ⁻¹' B ∩ Icc 0 Real.pi) := by
    ext t
    simp only [mem_inter_iff, mem_union, mem_Icc]
    constructor
    · rintro ⟨ht, hl, hr⟩
      rcases le_total t 0 with h | h
      · exact Or.inl ⟨ht, hl, h⟩
      · exact Or.inr ⟨ht, h, hr⟩
    · rintro (⟨ht, hl, hr⟩ | ⟨ht, hl, hr⟩)
      · exact ⟨ht, hl, hr.trans Real.pi_pos.le⟩
      · exact ⟨ht, (neg_nonpos.mpr Real.pi_pos.le).trans hl, hr⟩
  unfold m65CircleBoundaryMeasure
  rw [Measure.map_apply Proofs.M58.contDiff_angularPoint.continuous.measurable hA,
    Measure.restrict_apply' measurableSet_Icc, hBpre, hsplit]
  calc
    _ ≤ volume (Proofs.M58.angularPoint ⁻¹' B ∩ Icc (-Real.pi) 0) +
        volume (Proofs.M58.angularPoint ⁻¹' B ∩ Icc 0 Real.pi) := measure_union_le _ _
    _ ≤ ENNReal.ofReal Real.pi * (μH[1] : Measure LoopPlane) B +
        ENNReal.ofReal Real.pi * (μH[1] : Measure LoopPlane) B :=
      add_le_add (m65Angular_half_measure_le _ _ (by linarith) B)
        (m65Angular_half_measure_le _ _ (by linarith) B)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring





theorem m65SmoothCircle_map_bound (φ ψ : LoopPlane → LoopPlane)
    (hφ : Continuous φ) (hψ : ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 ψ z)
    (hφcircle : ∀ z, ‖z‖ = 1 → ‖φ z‖ = 1)
    (hψcircle : ∀ z, ‖z‖ = 1 → ‖ψ z‖ = 1)
    (hleft : ∀ z ∈ loopDiskSet, ψ (φ z) = z)
    (hright : ∀ z ∈ loopDiskSet, φ (ψ z) = z) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ m65CircleBoundaryMeasure.map φ ≤ C • m65CircleBoundaryMeasure := by
  have hψon : ContDiffOn ℝ 1 ψ loopDiskSet := fun z hz => (hψ z hz).contDiffWithinAt
  obtain ⟨K, hK⟩ := hψon.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 1)
    (isCompact_closedBall 0 1)
  refine ⟨ENNReal.ofReal (2 * Real.pi) * K, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.coe_ne_top, Measure.le_iff.mpr ?_⟩
  intro A hA
  have heq : φ ⁻¹' A ∩ {z | ‖z‖ = 1} = ψ '' (A ∩ {z | ‖z‖ = 1}) := by
    ext z
    constructor
    · rintro ⟨hzA, hz⟩
      exact ⟨φ z, ⟨hzA, hφcircle z hz⟩, hleft z (mem_closedBall_zero_iff.mpr hz.le)⟩
    · rintro ⟨w, ⟨hwA, hw⟩, rfl⟩
      refine ⟨?_, hψcircle w hw⟩
      change φ (ψ w) ∈ A
      rwa [hright w (mem_closedBall_zero_iff.mpr hw.le)]
  have hsub : A ∩ {z : LoopPlane | ‖z‖ = 1} ⊆ loopDiskSet :=
    fun z hz => mem_closedBall_zero_iff.mpr hz.2.le
  have hH := (hK.mono hsub).hausdorffMeasure_image_le (d := 1) zero_le_one
  simp only [ENNReal.rpow_one] at hH
  rw [Measure.map_apply hφ.measurable hA, Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal (2 * Real.pi) *
        (μH[1] : Measure LoopPlane) (φ ⁻¹' A ∩ {z | ‖z‖ = 1}) :=
      m65Boundary_hausdorff_upper _ (hφ.measurable hA)
    _ ≤ ENNReal.ofReal (2 * Real.pi) *
        (K * (μH[1] : Measure LoopPlane) (A ∩ {z | ‖z‖ = 1})) := by
      rw [heq]
      exact mul_le_mul_of_nonneg_left hH bot_le
    _ ≤ ENNReal.ofReal (2 * Real.pi) * (K * m65CircleBoundaryMeasure A) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (m65Boundary_hausdorff_lower A hA) bot_le) bot_le
    _ = _ := (mul_assoc _ _ _).symm

end PoincareConjecture
