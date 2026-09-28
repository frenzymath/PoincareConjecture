import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceHalfDisk











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M65StrictTrace

open M65Branch

variable {n : ℕ}



def halfDiskFrameDbar (H : ℂ → EuclideanSpace ℝ (Fin n))
    (L : EuclideanSpace ℝ (Fin n) → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (r : ℝ) (z : ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  dbarLinear ((fderiv ℝ L (H z)).comp
    (fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z))



def halfDiskFramedGradient (H : ℂ → EuclideanSpace ℝ (Fin n))
    (L : EuclideanSpace ℝ (Fin n) → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (r : ℝ) (z : ℂ) : Fin n → ℂ := L (H z) (halfDiskGradient H r z)



def halfDiskFramedMatrix {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) (H : ℂ → EuclideanSpace ℝ (Fin n))
    (L : EuclideanSpace ℝ (Fin n) → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (r : ℝ) (z : ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  (halfDiskFrameDbar H L r z + L (H z) * halfDiskHarmonicMatrix D H r z) *
    Ring.inverse (L (H z))



theorem halfDiskFrameDbar_eq
    {H : ℂ → EuclideanSpace ℝ (Fin n)}
    {L : EuclideanSpace ℝ (Fin n) → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    {r : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im})
    (hH : DifferentiableAt ℝ H z) (hL : DifferentiableAt ℝ L (H z)) :
    halfDiskFrameDbar H L r z = dbar (L ∘ H) z := by
  rw [halfDiskFrameDbar, fderivWithin_of_mem_nhds (halfDisk_mem_nhds hz)]
  exact congrArg dbarLinear (fderiv_comp z hL hH).symm




theorem halfDiskFramed_fields_continuousOn
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)}
    {L : EuclideanSpace ℝ (Fin n) → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    {r : ℝ} (hr : 0 < r) {V : Set (EuclideanSpace ℝ (Fin n))}
    (hV : IsOpen V) (hL : ContDiffOn ℝ ∞ L V)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHV : MapsTo H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) V)
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}, IsUnit (L (H z))) :
    ContinuousOn (halfDiskFramedGradient H L r)
        (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) ∧
      ContinuousOn (halfDiskFramedMatrix D H L r)
        (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨hF, hA⟩ := halfDisk_fields_continuousOn D hr hH
  have hLc := hL.continuousOn.comp hH.continuousOn hHV
  have hLd := (hL.continuousOn_fderiv_of_isOpen hV (by simp)).comp
    hH.continuousOn hHV
  have hHd := hH.continuousOn_fderivWithin
    (halfDisk_differential_domain hr).2.2.1 le_rfl
  have hB : ContinuousOn (halfDiskFrameDbar H L r)
      (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) :=
    dbarLinear.continuous.comp_continuousOn (hLd.clm_comp hHd)
  have hInv : ContinuousOn (fun z => Ring.inverse (L (H z)))
      (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) := by
    intro z hz
    obtain ⟨u, hu⟩ := hunit z hz
    have hi : ContDiffAt ℝ 1 Ring.inverse (L (H z)) := by
      simpa only [hu] using contDiffAt_ringInverse ℝ (n := 1) u
    exact hi.continuousAt.comp_continuousWithinAt (f := L ∘ H) (hLc z hz)
  exact ⟨hLc.clm_apply hF, (hB.add (hLc.mul hA)).mul hInv⟩



theorem halfDiskFramed_fields_equation
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)}
    {L : EuclideanSpace ℝ (Fin n) → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    {r : ℝ} {V : Set (EuclideanSpace ℝ (Fin n))}
    (hV : IsOpen V) (hL : ContDiffOn ℝ ∞ L V)
    (hH : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hHV : MapsTo H (ball (0 : ℂ) r ∩ {z | 0 < z.im}) V)
    (hunit : ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im}, IsUnit (L (H z)))
    (heq : ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z)) :
    ContDiffOn ℝ 1 (halfDiskFramedGradient H L r)
        (ball (0 : ℂ) r ∩ {z | 0 < z.im}) ∧
      ContDiffOn ℝ 1 (halfDiskFramedMatrix D H L r)
        (ball (0 : ℂ) r ∩ {z | 0 < z.im}) ∧
      ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im},
        dbar (halfDiskFramedGradient H L r) z =
          halfDiskFramedMatrix D H L r z (halfDiskFramedGradient H L r z) := by
  let U := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  obtain ⟨hF, hA, hFeq⟩ := halfDisk_fields_equation D hH heq
  have hLc : ContDiffOn ℝ ∞ (L ∘ H) U := hL.comp hH hHV
  have hLc1 : ContDiffOn ℝ 1 (L ∘ H) U := hLc.of_le (by simp)
  have hB : ContDiffOn ℝ 1 (halfDiskFrameDbar H L r) U := by
    have hder : ContDiffOn ℝ 1 (fderiv ℝ (L ∘ H)) U :=
      hLc.fderiv_of_isOpen (m := 1) hU (by decide)
    apply (dbarLinear.contDiff.comp_contDiffOn hder).congr
    intro z hz
    exact halfDiskFrameDbar_eq hz
      ((hH.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      ((hL.contDiffAt (hV.mem_nhds (hHV hz))).differentiableAt (by simp))
  have hInv : ContDiffOn ℝ 1 (fun z => Ring.inverse (L (H z))) U := by
    intro z hz
    obtain ⟨u, hu⟩ := hunit z hz
    have hi : ContDiffAt ℝ 1 Ring.inverse (L (H z)) := by
      simpa only [hu] using contDiffAt_ringInverse ℝ (n := 1) u
    exact (hi.comp z (hLc1.contDiffAt (hU.mem_nhds hz))).contDiffWithinAt
  let R := ContinuousLinearMap.restrictScalarsL ℂ (Fin n → ℂ) (Fin n → ℂ) ℝ ℝ
  refine ⟨(R.contDiff.comp_contDiffOn hLc1).clm_apply hF,
    (hB.add (hLc1.mul hA)).mul hInv, ?_⟩
  intro z hz
  have hHz := (hH.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hLz := (hL.contDiffAt (hV.mem_nhds (hHV hz))).differentiableAt (by simp)
  have hp := matrix_equation_under_frame
    ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
    ((hLc1.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
    (hunit z hz) (hFeq z hz)
  change dbar (fun w => L (H w) (halfDiskGradient H r w)) z = _
  simpa only [halfDiskFramedGradient, halfDiskFramedMatrix,
    halfDiskFrameDbar_eq hz hHz hLz, Function.comp_apply] using hp

end PoincareConjecture.M65StrictTrace
