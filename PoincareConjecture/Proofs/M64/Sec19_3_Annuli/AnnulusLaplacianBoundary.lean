import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapLocalFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture

theorem m64Annulus_laplacian_integral_eq_boundary
    {f : LoopPlane → ℝ} {O : Set LoopPlane} (hO : IsOpen O)
    (hdom : m64AnnulusDomain ⊆ O) (hf : ContDiffOn ℝ ∞ f O)
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1,
      fderiv ℝ f (annulusPoint curvePeriod s) (EuclideanSpace.single (0 : Fin 2) 1) =
        fderiv ℝ f (annulusPoint 0 s) (EuclideanSpace.single (0 : Fin 2) 1)) :
    (∫ p in m64AnnulusDomain,
      fderiv ℝ (fun q => fderiv ℝ f q (EuclideanSpace.single (0 : Fin 2) 1)) p
          (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ (fun q => fderiv ℝ f q (EuclideanSpace.single (1 : Fin 2) 1)) p
          (EuclideanSpace.single (1 : Fin 2) 1)) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        fderiv ℝ f (annulusPoint x 1) (EuclideanSpace.single (1 : Fin 2) 1) -
          fderiv ℝ f (annulusPoint x 0) (EuclideanSpace.single (1 : Fin 2) 1) := by
  let b0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  let D0 := fun p => fderiv ℝ f p b0
  let D1 := fun p => fderiv ℝ f p b1
  have hD0 : ContDiffOn ℝ ∞ D0 O :=
    (hf.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hD1 : ContDiffOn ℝ ∞ D1 O :=
    (hf.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hi0 : IntegrableOn (fun p => fderiv ℝ D0 p b0) m64AnnulusDomain volume :=
    (((hD0.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
      |>.mono hdom).integrableOn_compact m64AnnulusDomain_isCompact
  have hi1 : IntegrableOn (fun p => fderiv ℝ D1 p b1) m64AnnulusDomain volume :=
    (((hD1.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
      |>.mono hdom).integrableOn_compact m64AnnulusDomain_isCompact
  rw [integral_add hi0 hi1, m64Annulus_restrict_closed_eq_interior,
    m64Annulus_integral_horizontal_derivative_of_contDiffOn hO hdom hD0,
    m64Annulus_integral_vertical_derivative_of_contDiffOn hO hdom hD1]
  have hzero : (∫ s in Icc (0 : ℝ) 1,
      D0 (annulusPoint curvePeriod s) - D0 (annulusPoint 0 s)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact sub_eq_zero.mpr (hseam s hs)
  rw [hzero, zero_add]

end PoincareConjecture
