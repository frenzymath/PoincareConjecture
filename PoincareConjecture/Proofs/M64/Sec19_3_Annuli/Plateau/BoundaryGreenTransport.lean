import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusBoundaryHalfDisk
import PoincareConjecture.Proofs.M64.Mathlib.LocalIntervalFlux

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ
local notation "S" => interior m64AnnulusDomain

theorem m64Annulus_boundary_green_transport {x r : ℝ}
    (hr0 : 0 ≤ r) (hx : r < x) (hP : x + r < curvePeriod) (hr : r < 1)
    (u v oldU oldV : LoopPlane → ℝ) (oldB newB : ℝ → ℝ) (i : Fin 2)
    (ho : ContinuousOn oldB (Icc (0 : ℝ) curvePeriod))
    (hn : ContinuousOn newB (Icc (0 : ℝ) curvePeriod))
    (heq : EqOn oldB newB (Icc 0 curvePeriod \ Icc (x - r) (x + r)))
    (hgreen : ∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test →
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        v z * test z + u z * fderiv ℝ test z (basis i)) =
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        oldV (z + annulusPoint x 0) * test z +
          oldU (z + annulusPoint x 0) * fderiv ℝ test z (basis i)) +
      (basis 1) i *
        ((∫ s in (-r)..r, oldB (s + x) * test (s • basis 0)) -
          ∫ s in (-r)..r, newB (s + x) * test (s • basis 0)))
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) :
    (∫ p in closedBall (annulusPoint x 0) r ∩ S,
      v (p - annulusPoint x 0) * phi p +
        u (p - annulusPoint x 0) * fderiv ℝ phi p (basis i)) =
      (∫ p in closedBall (annulusPoint x 0) r ∩ S,
        oldV p * phi p + oldU p * fderiv ℝ phi p (basis i)) +
      (basis 1) i *
        ((∫ y in Icc (0 : ℝ) curvePeriod, oldB y * phi (annulusPoint y 0)) -
          ∫ y in Icc (0 : ℝ) curvePeriod, newB y * phi (annulusPoint y 0)) := by
  have hc : Continuous (fun y : ℝ => phi (annulusPoint y 0)) := by
    apply hphi.continuous.comp
    have hd : ContDiff ℝ 1 (fun y : ℝ => annulusPoint y 0) := by
      apply contDiff_euclidean.mpr
      intro j
      fin_cases j
      · exact contDiff_id
      · exact contDiff_const
    exact hd.continuous
  have hflux := m64Interval_local_flux hr0 (by linarith : 0 ≤ x - r) hP.le
    ((ho.mul hc.continuousOn).integrableOn_compact isCompact_Icc)
    ((hn.mul hc.continuousOn).integrableOn_compact isCompact_Icc)
    (fun y hy => congrArg (fun t => t * phi (annulusPoint y 0)) (heq hy))
  simp only [Pi.mul_apply] at hflux
  have hline (s : ℝ) : s • basis 0 + annulusPoint x 0 = annulusPoint (s + x) 0 := by
    ext j
    fin_cases j <;> simp [annulusPoint, EuclideanSpace.basisFun_apply]
  rw [m64Annulus_boundary_disk_integral hx hP hr,
    m64Annulus_boundary_disk_integral hx hP hr, hflux]
  simpa only [add_sub_cancel_right, fderiv_comp_add_right, hline] using
    hgreen (fun z => phi (z + annulusPoint x 0))
      (hphi.comp (contDiff_id.add contDiff_const))

end PoincareConjecture
