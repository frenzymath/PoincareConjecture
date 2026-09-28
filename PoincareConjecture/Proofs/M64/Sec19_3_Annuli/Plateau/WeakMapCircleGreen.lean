import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.DiskWeakGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarStrongApproximation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.H1SliceTrace

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

theorem m64CircleIntegral_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E) :
    (∫ t in Icc (-Real.pi) Real.pi, F t) =
      ∫ x in Icc (0 : ℝ) curvePeriod, F (x - Real.pi) := by
  have hT : (0 : ℝ) ≤ curvePeriod := by unfold curvePeriod; positivity
  have heq : curvePeriod - Real.pi = Real.pi := by unfold curvePeriod; ring
  have h := intervalIntegral.integral_comp_sub_right (a := (0 : ℝ)) (b := curvePeriod)
    F Real.pi
  simpa only [zero_sub, heq, intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    ← integral_Icc_eq_integral_Ioc] using h.symm

theorem m64WeakMap_local_circle_green
    {m : ℕ} {O : Set LoopPlane} (hO : IsOpen O)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O)
    (u : LoopPlane → EuclideanSpace ℝ (Fin m))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (hu : MemLp u 2 (volume.restrict O)) (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => u p b) O) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      let r := rho * Real.exp (-s)
      ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
        (∫ p in Metric.closedBall a r, phi p • V i p) +
          (∫ p in Metric.closedBall a r,
            fderiv ℝ phi p (EuclideanSpace.single i 1) • u p) =
          r • ∫ x in Icc (0 : ℝ) curvePeriod,
            angularPoint (x - Real.pi) i •
              (phi (a + r • angularPoint (x - Real.pi)) •
                u (a + r • angularPoint (x - Real.pi))) := by
  let P := m64MorreyPolarStrip a rho
  let Z := m64MorreyPolarAngularColumn a rho V
  have huK := hu.mono_measure (Measure.restrict_mono hKO le_rfl)
  have hVK (i : Fin 2) := (hV i).mono_measure (Measure.restrict_mono hKO le_rfl)
  obtain ⟨f, hf, hval, hcol⟩ := m64WeakMap_inner_strong_approximation
    hO (isCompact_closedBall a rho) hKO u V hu hV hw
  obtain ⟨huP, hZ, hvalP, hcolP⟩ :=
    m64Polar_strong_transfer a hrho u V huK hVK f hf hval hcol
  have hperiod (j : ℕ) (x s : ℝ) :
      (f j ∘ P) (annulusPoint (x + curvePeriod) s) = (f j ∘ P) (annulusPoint x s) :=
    congrArg (f j) (m64MorreyPolarStrip_periodic a rho x s)
  have hslices := m64Annulus_h1_slices_of_strong_approximation
    (fun j => f j ∘ P)
    (fun j => ((hf j).comp (m64MorreyPolarStrip_contDiff a rho)).of_le (by simp))
    hperiod (u ∘ P) Z huP hZ hvalP hcolP
  have hfi (j : ℕ) : MemLp (f j) 2 (volume.restrict (Metric.closedBall a rho)) := by
    apply (memLp_two_iff_integrable_sq_norm (hf j).continuous.aestronglyMeasurable).mpr
    exact ((hf j).continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a rho)
  have hDi (j : ℕ) (i : Fin 2) : MemLp
      (fun p => fderiv ℝ (f j) p (EuclideanSpace.single i 1)) 2
      (volume.restrict (Metric.closedBall a rho)) := by
    have hc := ((hf j).continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1))
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    exact (hc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall a rho)
  filter_upwards [hslices, ae_restrict_mem measurableSet_Icc] with s hs hsI
  obtain ⟨_, k, W, hk, _, _, hWu, huni, _, _⟩ := hs
  let r := rho * Real.exp (-s)
  have hr : 0 < r := mul_pos hrho (Real.exp_pos _)
  have hrrho : r ≤ rho := mul_le_of_le_one_right hrho.le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hsI.1))
  have hKK : Metric.closedBall a r ⊆ Metric.closedBall a rho :=
    Metric.closedBall_subset_closedBall hrrho
  have huv := huK.mono_measure (Measure.restrict_mono hKK le_rfl)
  have hVv (i : Fin 2) := (hVK i).mono_measure (Measure.restrict_mono hKK le_rfl)
  have hvall := m64StrongSquare_restrict hKK f u
    (fun j => (memLp_two_iff_integrable_sq_norm ((hfi j).sub huK).aestronglyMeasurable).mp
      ((hfi j).sub huK)) hval
  have hcoll (i : Fin 2) := m64StrongSquare_restrict hKK
    (fun j p => fderiv ℝ (f j) p (EuclideanSpace.single i 1)) (V i)
    (fun j => (memLp_two_iff_integrable_sq_norm
      ((hDi j i).sub (hVK i)).aestronglyMeasurable).mp ((hDi j i).sub (hVK i))) (hcol i)
  have hgeom (t : ℝ) : P (annulusPoint (t + Real.pi) s) = a + r • angularPoint t := by
    change a + r • angularPoint (t + Real.pi - Real.pi) = _
    rw [add_sub_cancel_right]
  have htrace : TendstoUniformlyOn (fun j t => f (k j) (a + r • angularPoint t))
      (fun t => W (t + Real.pi)) atTop (Icc (-Real.pi) Real.pi) := by
    have hh := (huni.comp (fun t => t + Real.pi)).mono (show
        Icc (-Real.pi) Real.pi ⊆ (fun t => t + Real.pi) ⁻¹' Icc (0 : ℝ) curvePeriod from by
      intro t ht
      change 0 ≤ t + Real.pi ∧ t + Real.pi ≤ curvePeriod
      unfold curvePeriod
      constructor <;> linarith [ht.1, ht.2])
    simpa +instances only [Function.comp_def, hgeom] using! hh
  dsimp only
  intro phi hphi i
  have hgreen := m64Disk_weak_green_of_strong_approximation a hr
    (fun j => f (k j)) (fun j => (hf (k j)).of_le (by simp)) u V
    (fun t => W (t + Real.pi)) huv hVv
    (hvall.comp hk.tendsto_atTop) (fun i => (hcoll i).comp hk.tendsto_atTop) htrace phi hphi i
  rw [m64CircleIntegral_shift] at hgreen
  simp only [sub_add_cancel] at hgreen
  refine hgreen.trans (congrArg (fun z => r • z) (integral_congr_ae ?_))
  filter_upwards [hWu] with x hx
  change W x = u (a + r • angularPoint (x - Real.pi)) at hx
  rw [hx]

end PoincareConjecture
