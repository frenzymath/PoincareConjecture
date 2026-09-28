import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.BoundaryPolarEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicCircleShift









set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64

local notation "S" => interior m64AnnulusDomain
local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)



def angularStripShift (d : ℝ) (p : LoopPlane) : LoopPlane :=
  annulusPoint (p 0 + d) (p 1)



theorem angularStripShift_eq_add (d : ℝ) (p : LoopPlane) :
    angularStripShift d p = annulusPoint d 0 + p := by
  ext i
  fin_cases i <;> simp [angularStripShift, annulusPoint, add_comm]



theorem angularStripShift_contDiff (d : ℝ) : ContDiff ℝ ∞ (angularStripShift d) := by
  rw [show angularStripShift d = fun p => annulusPoint d 0 + p from
    funext (angularStripShift_eq_add d)]
  exact contDiff_const.add contDiff_id




theorem periodic_strip_integral_shift
    (f : LoopPlane → ℝ) (hc : ContinuousOn f Strip)
    (hp : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hi : IntegrableOn f S) (d : ℝ) :
    IntegrableOn (f ∘ angularStripShift d) S ∧
      (∫ p in S, f (angularStripShift d p)) = ∫ p in S, f p := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hmap : MapsTo (angularStripShift d) S Strip := by
    intro p hp
    have hh := (m64AnnulusInterior_coordinates p).mp hp
    exact ⟨hh.2.2.1, hh.2.2.2⟩
  have hshiftc : ContinuousOn (f ∘ angularStripShift d) S :=
    hc.comp (angularStripShift_contDiff d).continuous.continuousOn hmap
  have hm := hshiftc.aestronglyMeasurable (μ := volume) isOpen_interior.measurableSet
  have hprod := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hi
  have hprodMeas := hm.comp_measurePreserving m64AnnulusPoint_measurePreserving
  have hslice : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      Integrable (fun x => f (angularStripShift d (annulusPoint x s)))
        (volume.restrict (Icc (0 : ℝ) curvePeriod)) := by
    filter_upwards [hprod.prod_left_ae] with s hs
    exact m64Periodic_integrableOn_shift hP (fun x => hp x s) hs d
  have hnorm : Integrable (fun s => ∫ x in Icc (0 : ℝ) curvePeriod,
      ‖f (angularStripShift d (annulusPoint x s))‖) (volume.restrict (Icc (0 : ℝ) 1)) := by
    apply hprod.integral_norm_prod_right.congr
    filter_upwards with s
    have hnormPeriod : Function.Periodic (fun x => ‖f (annulusPoint x s)‖) curvePeriod :=
      fun x => congrArg norm (hp x s)
    exact (m64Periodic_integral_shift hP hnormPeriod d).symm
  have hprodShift := (integrable_prod_iff' hprodMeas).mpr ⟨hslice, hnorm⟩
  have hshift := (m64AnnulusPoint_measurePreserving.integrable_comp hm).mp hprodShift
  refine ⟨hshift, ?_⟩
  change (∫ p in S, (f ∘ angularStripShift d) p) = ∫ p in S, f p
  rw [m64AnnulusInteriorIntegral_eq_iterated_swap_integrable _ hshift,
    m64AnnulusInteriorIntegral_eq_iterated_swap_integrable _ hi]
  apply integral_congr_ae
  filter_upwards with s
  exact m64Periodic_integral_shift (f := fun x => f (annulusPoint x s)) hP (fun x => hp x s) d



theorem phaseGradientDensity_angular_shift (L : LoopPlane → ℝ) (d : ℝ) (p : LoopPlane) :
    phaseGradientDensity (L ∘ angularStripShift d) p =
      phaseGradientDensity L (angularStripShift d p) := by
  have hfun : L ∘ angularStripShift d = fun q => L (annulusPoint d 0 + q) :=
    funext (fun q => congrArg L (angularStripShift_eq_add d q))
  simp only [phaseGradientDensity, hfun, fderiv_comp_add_left, angularStripShift_eq_add]



theorem phaseGradientDensity_periodic
    (L : LoopPlane → ℝ) {d : ℝ}
    (hp : ∀ x s, L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d) :
    ∀ x s, phaseGradientDensity L (annulusPoint (x + curvePeriod) s) =
      phaseGradientDensity L (annulusPoint x s) := by
  have hfun : L ∘ angularStripShift curvePeriod = fun p => L p + d := by
    funext p
    have hh := hp (p 0) (p 1)
    have heq : annulusPoint (p 0) (p 1) = p := by
      ext i
      fin_cases i <;> simp [annulusPoint]
    simpa only [Function.comp_apply, angularStripShift, heq] using hh
  intro x s
  have hh := phaseGradientDensity_angular_shift L curvePeriod (annulusPoint x s)
  rw [hfun] at hh
  simpa only [phaseGradientDensity, fderiv_add_const, angularStripShift, annulusPoint,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hh.symm




theorem phase_angular_shift_energy
    (L : LoopPlane → ℝ) (hL : ContDiffOn ℝ 1 L Strip) {d : ℝ}
    (hp : ∀ x s, L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d)
    (hi : IntegrableOn (phaseGradientDensity L) S) (a : ℝ) :
    IntegrableOn (phaseGradientDensity (L ∘ angularStripShift a)) S ∧
      (∫ p in S, phaseGradientDensity (L ∘ angularStripShift a) p) =
        ∫ p in S, phaseGradientDensity L p := by
  have hstrip : IsOpen Strip := isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous
  have hDf : ContinuousOn (fderiv ℝ L) Strip :=
    (hL.fderiv_of_isOpen hstrip (m := 0) (by norm_num)).continuousOn
  have hc : ContinuousOn (phaseGradientDensity L) Strip :=
    ((hDf.clm_apply continuousOn_const).pow 2).add
      ((hDf.clm_apply continuousOn_const).pow 2)
  have hh := periodic_strip_integral_shift (phaseGradientDensity L) hc
    (phaseGradientDensity_periodic L hp) hi a
  have heq : phaseGradientDensity (L ∘ angularStripShift a) =
      phaseGradientDensity L ∘ angularStripShift a :=
    funext (phaseGradientDensity_angular_shift L a)
  rw [heq]
  exact hh

end PoincareConjecture.M64
