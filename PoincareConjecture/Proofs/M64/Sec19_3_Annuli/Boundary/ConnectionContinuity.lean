import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.HalfDiskCollarRectangle

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open M65Gauss M65StrictTrace

theorem frame_connection_continuousOn {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {H T N : ℂ → EuclideanSpace ℝ (Fin n)} {U : Set ℂ} (hU : IsOpen U)
    (hH : ContDiffOn ℝ 1 H U) (hT : ContDiffOn ℝ 1 T U) (hN : ContinuousOn N U) :
    ContinuousOn (fun z => g.inner (H z)
      (covariantDerivativeAlongMap D H T z 1) (N z)) U := by
  have hG : ContinuousOn (fun z => g.euclideanCoefficients (H z)) U :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).continuous.comp_continuousOn
      hH.continuousOn
  have hDH : ContinuousOn (fun z => fderiv ℝ H z 1) U :=
    ((hH.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn).clm_apply continuousOn_const
  have hDT : ContinuousOn (fun z => fderiv ℝ T z 1) U :=
    ((hT.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn).clm_apply continuousOn_const
  have hGamma : ContinuousOn (fun z => connectionCoefficient D (H z)) U :=
    (contDiff_connectionCoefficient D).continuous.comp_continuousOn hH.continuousOn
  exact (hG.clm_apply (hDT.add ((hGamma.clm_apply hDH).clm_apply hT.continuousOn))).clm_apply hN

theorem halfDisk_boundary_connection_continuousOn {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)}
    {V : ℂ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    {R e : ℝ} (hR : 0 < R) (heR : e ≤ R)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    (hV : ContinuousOn V (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    (hT : ∀ t ∈ Icc (-e) e, ContDiffAt ℝ 1 (fun s : ℝ => (V (s : ℂ)).1) t) :
    ContinuousOn (fun t : ℝ => g.inner (H (t : ℂ))
      (deriv (fun s : ℝ => (V (s : ℂ)).1) t +
        connectionCoefficient D (H (t : ℂ))
          (fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) (t : ℂ) 1)
          (V (t : ℂ)).1) (V (t : ℂ)).2) (Icc (-e) e) := by
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  let J := Icc (-e) e
  have hmap : MapsTo (fun t : ℝ => (t : ℂ)) J K := by
    intro t ht
    refine ⟨mem_closedBall_zero_iff.mpr ?_, by simp⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_le.mpr ht).trans heR
  have hH0 : ContinuousOn (fun t : ℝ => H (t : ℂ)) J :=
    hH.continuousOn.comp continuous_ofReal.continuousOn hmap
  have hV0 : ContinuousOn (fun t : ℝ => V (t : ℂ)) J :=
    hV.comp continuous_ofReal.continuousOn hmap
  have hD := hH.continuousOn_fderivWithin (halfDisk_differential_domain hR).2.2.1 le_rfl
  have hDH0 : ContinuousOn (fun t : ℝ => fderivWithin ℝ H K (t : ℂ) 1) J :=
    (hD.clm_apply continuousOn_const).comp continuous_ofReal.continuousOn hmap
  have hDT : ContinuousOn (deriv (fun s : ℝ => (V (s : ℂ)).1)) J := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    simpa only [fderiv_apply_one_eq_deriv] using
      (((hT t ht).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
        (continuousAt_const (x := t) (y := (1 : ℝ))))
  have hG : ContinuousOn (fun t : ℝ => g.euclideanCoefficients (H (t : ℂ))) J :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).continuous.comp_continuousOn
      hH0
  have hGamma : ContinuousOn (fun t : ℝ => connectionCoefficient D (H (t : ℂ))) J :=
    (contDiff_connectionCoefficient D).continuous.comp_continuousOn hH0
  exact (hG.clm_apply (hDT.add ((hGamma.clm_apply hDH0).clm_apply hV0.fst))).clm_apply hV0.snd

end PoincareConjecture.M64
