import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryGreenTransport
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryGreenPairings
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularSlice

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ
local notation "S" => interior m64AnnulusDomain
local notation "I" => Icc (0 : ℝ) curvePeriod

theorem m64Annulus_boundary_vector_green {N : ℕ} {x r : ℝ}
    (hr0 : 0 ≤ r) (hx : r < x) (hP : x + r < curvePeriod) (hr : r < 1)
    (u v oldU oldV : LoopPlane → EuclideanSpace ℝ (Fin N))
    (oldB newB : ℝ → EuclideanSpace ℝ (Fin N)) (i : Fin 2)
    (hu : MemLp u 2 (volume.restrict (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})))
    (hv : MemLp v 2 (volume.restrict (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})))
    (hoU : MemLp oldU 2 (volume.restrict (closedBall (annulusPoint x 0) r ∩ S)))
    (hoV : MemLp oldV 2 (volume.restrict (closedBall (annulusPoint x 0) r ∩ S)))
    (ho : ContinuousOn oldB I) (hn : ContinuousOn newB I)
    (heq : EqOn oldB newB (I \ Icc (x - r) (x + r)))
    (hgreen : ∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ j : Fin N,
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        v z j * test z + u z j * fderiv ℝ test z (basis i)) =
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        oldV (z + annulusPoint x 0) j * test z +
          oldU (z + annulusPoint x 0) j * fderiv ℝ test z (basis i)) +
      (basis 1) i *
        ((∫ s in (-r)..r, oldB (s + x) j * test (s • basis 0)) -
          ∫ s in (-r)..r, newB (s + x) j * test (s • basis 0)))
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) :
    (∫ p in closedBall (annulusPoint x 0) r ∩ S, phi p • v (p - annulusPoint x 0)) +
      (∫ p in closedBall (annulusPoint x 0) r ∩ S,
        fderiv ℝ phi p (basis i) • u (p - annulusPoint x 0)) =
      (∫ p in closedBall (annulusPoint x 0) r ∩ S, phi p • oldV p) +
      (∫ p in closedBall (annulusPoint x 0) r ∩ S, fderiv ℝ phi p (basis i) • oldU p) +
      if i = 1 then
        (∫ y in I, phi (annulusPoint y 0) • oldB y) -
          ∫ y in I, phi (annulusPoint y 0) • newB y else 0 := by
  have hp : MemLp phi 2 (volume.restrict (closedBall (annulusPoint x 0) r ∩ S)) :=
    (m64Annulus_continuous_memLp_two hphi.continuous).mono_measure
    (Measure.restrict_mono inter_subset_right le_rfl)
  have hq : MemLp (fun p => fderiv ℝ phi p (basis i)) 2
      (volume.restrict (closedBall (annulusPoint x 0) r ∩ S)) :=
    (m64Annulus_continuous_memLp_two
    ((hphi.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const (y := basis i)))).mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)
  have hc := hphi.continuous.comp (m64Source_annulusPoint_contDiff 0).continuous
  have hio : IntegrableOn (fun y => phi (annulusPoint y 0) • oldB y) I :=
    (hc.continuousOn.smul ho).integrableOn_compact isCompact_Icc
  have hin : IntegrableOn (fun y => phi (annulusPoint y 0) • newB y) I :=
    (hc.continuousOn.smul hn).integrableOn_compact isCompact_Icc
  ext j
  have hflux : ((∫ y in I, phi (annulusPoint y 0) • oldB y) -
      ∫ y in I, phi (annulusPoint y 0) • newB y) j =
      (∫ y in I, oldB y j * phi (annulusPoint y 0)) -
        ∫ y in I, newB y j * phi (annulusPoint y 0) := by
    rw [PiLp.sub_apply, eval_integral_piLp hio.eval_piLp j,
      eval_integral_piLp hin.eval_piLp j]
    simp only [PiLp.smul_apply, smul_eq_mul, mul_comm]
  rw [m64L2_vector_green_pairing (m64Annulus_boundary_disk_memLp hu)
    (m64Annulus_boundary_disk_memLp hv) hp hq j, PiLp.add_apply,
    m64L2_vector_green_pairing hoU hoV hp hq j]
  have hphysical := m64Annulus_boundary_green_transport hr0 hx hP hr
    (fun z => u z j) (fun z => v z j) (fun z => oldU z j) (fun z => oldV z j)
    (fun y => oldB y j) (fun y => newB y j) i
    ((EuclideanSpace.proj j).continuous.comp_continuousOn ho)
    ((EuclideanSpace.proj j).continuous.comp_continuousOn hn)
    (fun y hy => congrArg (fun z => z j) (heq hy))
    (fun test htest => hgreen test htest j) phi hphi
  rw [hphysical]
  congr 1
  fin_cases i <;> simp [EuclideanSpace.basisFun_apply, hflux]

theorem m64Annulus_boundary_scalar_green {x r : ℝ}
    (hr0 : 0 ≤ r) (hx : r < x) (hP : x + r < curvePeriod) (hr : r < 1)
    (u v oldU oldV : LoopPlane → ℝ) (oldB newB : ℝ → ℝ) (i : Fin 2)
    (hu : MemLp u 2 (volume.restrict (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})))
    (hv : MemLp v 2 (volume.restrict (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})))
    (hoU : MemLp oldU 2 (volume.restrict (closedBall (annulusPoint x 0) r ∩ S)))
    (hoV : MemLp oldV 2 (volume.restrict (closedBall (annulusPoint x 0) r ∩ S)))
    (ho : ContinuousOn oldB I) (hn : ContinuousOn newB I)
    (heq : EqOn oldB newB (I \ Icc (x - r) (x + r)))
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
    (∫ p in closedBall (annulusPoint x 0) r ∩ S, phi p * v (p - annulusPoint x 0)) +
      (∫ p in closedBall (annulusPoint x 0) r ∩ S,
        fderiv ℝ phi p (basis i) * u (p - annulusPoint x 0)) =
      (∫ p in closedBall (annulusPoint x 0) r ∩ S, phi p * oldV p) +
      (∫ p in closedBall (annulusPoint x 0) r ∩ S, fderiv ℝ phi p (basis i) * oldU p) +
      if i = 1 then
        (∫ y in I, phi (annulusPoint y 0) * oldB y) -
          ∫ y in I, phi (annulusPoint y 0) * newB y else 0 := by
  have hp : MemLp phi 2 (volume.restrict (closedBall (annulusPoint x 0) r ∩ S)) :=
    (m64Annulus_continuous_memLp_two hphi.continuous).mono_measure
    (Measure.restrict_mono inter_subset_right le_rfl)
  have hq : MemLp (fun p => fderiv ℝ phi p (basis i)) 2
      (volume.restrict (closedBall (annulusPoint x 0) r ∩ S)) :=
    (m64Annulus_continuous_memLp_two
    ((hphi.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const (y := basis i)))).mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)
  rw [m64L2_scalar_green_pairing (m64Annulus_boundary_disk_memLp hu)
    (m64Annulus_boundary_disk_memLp hv) hp hq,
    m64L2_scalar_green_pairing hoU hoV hp hq]
  rw [m64Annulus_boundary_green_transport hr0 hx hP hr u v oldU oldV oldB newB i
    ho hn heq hgreen phi hphi]
  congr 1
  fin_cases i <;> simp [EuclideanSpace.basisFun_apply, mul_comm]

end PoincareConjecture
