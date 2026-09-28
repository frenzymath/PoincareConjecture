import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundarySubdivision

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

theorem boundary_curvature_flux_continuous (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ t : ℝ, curveVelocity (n := 3) (periodicFreeLoop gamma) t ≠ 0)
    (W : (p : M) → TangentSpace (𝓡 3) p)
    (hW : ∀ s, W (periodicFreeLoop gamma s) = M65Filling.loopCurvature connection gamma s) :
    Continuous (fun theta => g.inner (S.disk.map (Proofs.M58.angularPoint theta))
      (W (S.disk.map (Proofs.M58.angularPoint theta)))
      (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
        (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta))) := by
  let B := fun theta => g.inner (S.disk.map (Proofs.M58.angularPoint theta))
    (W (S.disk.map (Proofs.M58.angularPoint theta)))
    (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
      (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta))
  apply continuous_iff_continuousAt.mpr
  intro a
  obtain ⟨gE, DE, r, d, C, F, hr, hd, hdr, _hC, hH, hF, _hF1,
      _hDF, _hholder, _hradial, hboundary⟩ :=
    S.exists_angular_collar hinj hsmooth hregular W hW a
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let P := e ∘ boundaryCoordinate (e.symm (Proofs.M58.angularPoint a))
  let H := (chartAt LoopAmbient (S.disk.map (Proofs.M58.angularPoint a))) ∘ S.disk.map ∘ P
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let J := Icc (-d) d
  let T := fun t : ℝ => (F (t : ℂ)).1
  let A := fun t : ℝ => gE.inner (H (t : ℂ))
    (deriv T t + connectionCoefficient DE (H (t : ℂ))
      (fderivWithin ℝ H K (t : ℂ) 1) (T t)) (F (t : ℂ)).2
  have hmap : MapsTo (fun t : ℝ => (t : ℂ)) J K := by
    intro t ht
    refine ⟨mem_closedBall_zero_iff.mpr ?_, by simp⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_le.mpr ht).trans (by linarith)
  have hJ : J ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) hd
  have h0 : (0 : ℝ) ∈ J := ⟨by linarith, hd.le⟩
  have hH0 : ContinuousAt (fun t : ℝ => H (t : ℂ)) 0 :=
    (hH.continuousOn.comp continuous_ofReal.continuousOn hmap).continuousAt hJ
  have hF0 : ContinuousAt (fun t : ℝ => F (t : ℂ)) 0 :=
    (hF.comp continuous_ofReal.continuousOn hmap).continuousAt hJ
  have hDH0 : ContinuousAt (fun t : ℝ => fderivWithin ℝ H K (t : ℂ) 1) 0 :=
    (((hH.continuousOn_fderivWithin
      (halfDisk_differential_domain hr).2.2.1 le_rfl).clm_apply continuousOn_const).comp
        continuous_ofReal.continuousOn hmap).continuousAt hJ
  have hT0 : ContDiffAt ℝ 1 T 0 := (hboundary 0 h0).1
  have hDT : ContinuousAt (deriv T) 0 := by
    simpa only [fderiv_apply_one_eq_deriv] using
      ((hT0.fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
        (continuousAt_const (x := (0 : ℝ)) (y := (1 : ℝ))))
  have hG : ContinuousAt (fun t : ℝ => gE.euclideanCoefficients (H (t : ℂ))) 0 :=
    (contDiff_iff_contDiffAt.mpr gE.contDiffAt_euclideanCoefficients).continuous.continuousAt.comp
      hH0
  have hGamma : ContinuousAt (fun t : ℝ => connectionCoefficient DE (H (t : ℂ))) 0 :=
    (contDiff_connectionCoefficient DE).continuous.continuousAt.comp hH0
  have hA : ContinuousAt A 0 :=
    (hG.clm_apply (hDT.add ((hGamma.clm_apply hDH0).clm_apply hF0.fst))).clm_apply hF0.snd
  have hshift : ContinuousAt (fun s : ℝ => -A (s - a)) a :=
    hA.neg.comp_of_eq (continuousAt_id.sub_const a) (sub_self a)
  apply hshift.congr
  have hnear : ∀ᶠ s : ℝ in 𝓝 a, s - a ∈ J :=
    (show Tendsto (fun s : ℝ => s - a) (𝓝 a) (𝓝 0) by
      simpa only [id_eq, sub_self] using (continuousAt_id.sub_const a :
        ContinuousAt (fun s : ℝ => s - a) a)) hJ
  filter_upwards [hnear] with s hs
  change -A (s - a) = B s
  have hh : A (s - a) = -B ((s - a) + a) := (hboundary (s - a) hs).2
  rw [hh, neg_neg, sub_add_cancel]

omit [T2Space M] in

theorem exists_regular_annulus (S : M65MinimalDisk g connection gamma) :
    ∃ R0 : ℝ, 0 < R0 ∧ R0 < 1 ∧
      ∀ z : LoopPlane, R0 < ‖z‖ → ‖z‖ < 1 → 0 < S.conformalFactor z := by
  classical
  let E : Set LoopPlane := {z | ‖z‖ < 1 ∧ S.conformalFactor z = 0}
  have hE : E.Finite := S.conformalFactor_finite_zeros.subset (by
    intro z hz
    exact ⟨by simpa only [loopDiskSet, mem_closedBall_zero_iff] using hz.1.le, hz.2⟩)
  obtain ⟨z0, hz0, hmax⟩ := (hE.insert 0).isCompact.exists_isMaxOn
    (insert_nonempty 0 E) continuous_norm.continuousOn
  have hz01 : ‖z0‖ < 1 := by
    rcases hz0 with h | h
    · simp only [h, norm_zero]; norm_num
    · exact h.1
  refine ⟨(‖z0‖ + 1) / 2, by positivity, by linarith, ?_⟩
  intro z hz hz1
  apply lt_of_le_of_ne (S.conformalFactor_nonneg z)
  intro hzero
  have hle : ‖z‖ ≤ ‖z0‖ := hmax (mem_insert_of_mem 0 ⟨hz1, hzero.symm⟩)
  linarith

omit [T2Space M] in

theorem radial_log_flux_continuous (S : M65MinimalDisk g connection gamma)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hpos : ∀ z : LoopPlane, ‖z‖ = R → 0 < S.conformalFactor z) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    Continuous (fun theta =>
      let z := e.symm (R • Proofs.M58.angularPoint theta)
      fderiv ℝ (fun w => Real.log (S.conformalFactor (e w))) z z / 2) := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let z := fun theta => e.symm (R • Proofs.M58.angularPoint theta)
  let L := fun w => Real.log (S.conformalFactor (e w))
  have hz : Continuous z := e.symm.continuous.comp
    (Proofs.M58.contDiff_angularPoint.continuous.const_smul R)
  have hnorm (theta : ℝ) : ‖z theta‖ = R := by
    change ‖orthonormalBasisOneI.repr.symm (R • Proofs.M58.angularPoint theta)‖ = R
    rw [orthonormalBasisOneI.repr.symm.norm_map, norm_smul,
      Real.norm_eq_abs, abs_of_pos hR, Proofs.M58.norm_angularPoint, mul_one]
  apply continuous_iff_continuousAt.mpr
  intro theta
  have hloc : ContDiffAt ℝ 1 L (z theta) :=
    ((S.conformalFactor_complex_contDiffOn.contDiffAt (isOpen_ball.mem_nhds
      (mem_ball_zero_iff.mpr (hnorm theta ▸ hR1)))).log (by
        apply ne_of_gt
        apply hpos
        simpa only [orthonormalBasisOneI.repr.norm_map] using hnorm theta)).of_le (by simp)
  exact ((((hloc.fderiv_right (m := 0) (by norm_num)).continuousAt.comp
    hz.continuousAt).clm_apply hz.continuousAt).div_const 2)

end PoincareConjecture.M65MinimalDisk
