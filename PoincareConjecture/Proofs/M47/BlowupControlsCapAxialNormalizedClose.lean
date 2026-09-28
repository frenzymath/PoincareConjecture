import PoincareConjecture.Proofs.M47.BlowupControlsCapAxialNormalizedEnergy
import PoincareConjecture.Proofs.M47.BlowupControlsCapModelScalarEnergy
import PoincareConjecture.Proofs.M47.BlowupControlsCapNormalizationAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

theorem cap_native_axial_normalized_close
    {gamma epsilon beta lambda : ℝ} (hgamma : 0 < gamma)
    (hsmall : gamma ≤ 1 / 1200) (hepsilon : 0 < epsilon)
    (haccuracy : 6 * gamma ≤ epsilon)
    (B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (hclose : RoundCylinderClose gamma 0 (fun z v w => B z v w))
    (g1 : RiemannianMetric 3 E) (D1 : LeviCivitaData g1)
    (q : UnitTwoSphere) {U : Set E} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E2 q)
        (M35.cylinderCoordinateEquiv x) i j)
    (c : ℝ) (hc : c ∈ Ioo (-gamma⁻¹) gamma⁻¹)
    (hx : M35.cylinderCoordinateEquiv.symm (0, c) ∈ U)
    (hscalar : beta = D1.scalarCurvature (M35.cylinderCoordinateEquiv.symm (0, c)))
    (hlambda : 0 ≤ lambda) (hscale : beta * lambda ^ 2 = 1)
    (hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-gamma⁻¹) gamma⁻¹) :
    RoundCylinderClose epsilon 0 (fun z v w => beta * neckAxialTensorPullback lambda c
      (fun z v w => B z v w) z v w) := by
  let D0 := M35.cylinderEuclideanConnection 0 zero_lt_one
  obtain ⟨bound, hbound, hjet⟩ := hclose.2
  have herror := cap_model_scalar_difference_le hgamma (by linarith only [hsmall])
    (le_refl (0 : ℝ)) (fun z v w => B z v w) hclose g1 D1 D0 q hU hcoeff c hc hx
  have habs : |beta - 1| ≤ 4 * gamma := by
    norm_num only [sub_zero, div_one] at herror
    rw [← hscalar] at herror
    linarith only [herror, hgamma]
  have hlower : 1 - 4 * gamma ≤ beta := by linarith [(abs_le.mp habs).1]
  have hupper : beta ≤ (301 / 300 : ℝ) := by linarith [(abs_le.mp habs).2]
  have hbeta : 0 < beta := by linarith only [hlower, hsmall]
  have hcenter : (beta - 1) ^ 2 ≤ (16 / 5 : ℝ) ^ 2 * bound := by
    rw [hscalar]
    exact (cap_model_scalar_difference_sq_le_jet hgamma hsmall (fun z v w => B z v w)
      hclose g1 D1 D0 q hU hcoeff c hc hx).trans
      (mul_le_mul_of_nonneg_left (hjet (q, c) hc) (sq_nonneg _))
  have horder : (⌊epsilon⁻¹⌋₊ : ℝ) * gamma ≤ 1 / 6 := by
    calc
      _ ≤ epsilon⁻¹ * gamma := mul_le_mul_of_nonneg_right
        (Nat.floor_le (inv_nonneg.mpr hepsilon.le)) hgamma.le
      _ ≤ 1 / 6 := by
        rw [inv_mul_eq_div, div_le_iff₀ hepsilon]
        linarith only [haccuracy]
  have horders : ⌊epsilon⁻¹⌋₊ ≤ ⌊gamma⁻¹⌋₊ := by
    apply Nat.floor_mono
    simpa only [one_div] using one_div_le_one_div_of_le hgamma
      (by linarith only [haccuracy, hgamma] : gamma ≤ epsilon)
  refine ⟨?_, 36 * bound, cap_normalization_strict_witness hgamma.le haccuracy hbound, ?_⟩
  · intro q' i j
    have hA : ContDiff ℝ ∞ (neckAxialCoordinate lambda c) :=
      contDiff_fst.prodMk ((contDiff_const.mul contDiff_snd).add contDiff_const)
    have hmaps : MapsTo (neckAxialCoordinate lambda c)
        ((chartAt E2 q').target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)
        ((chartAt E2 q').target ×ˢ Ioo (-gamma⁻¹) gamma⁻¹) :=
      fun p hp => ⟨hp.1, hdomain p.2 hp.2⟩
    have hcomp := (hclose.1 q' i j).comp hA.contDiffOn hmaps
    have hprod : ContDiffOn ℝ ∞ (fun p : V =>
        (beta * neckAxialWeight lambda i * neckAxialWeight lambda j) *
          roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E2 q')
            (neckAxialCoordinate lambda c p) i j)
        ((chartAt E2 q').target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) :=
      contDiffOn_const.mul hcomp
    apply hprod.congr
    intro p _
    change beta * roundCylinderTensorCoefficient
      (neckAxialTensorPullback lambda c (fun z v w => B z v w)) (chartAt E2 q') p i j = _
    rw [roundCylinderTensorCoefficient_neckAxialTensorPullback]
    ring
  · intro z hz
    have hold := (M34.roundCylinderJetErrorSquared_mono_order zero_lt_one
      (fun z v w => B z v w) horders (neckAxialSpaceMap lambda c z)).trans
      (hjet (neckAxialSpaceMap lambda c z) (hdomain z.2 hz))
    exact cap_native_axial_normalized_energy_le hgamma.le hbeta hupper hlower hlambda
      hscale hcenter c B hclose.1 _ horder z (hdomain z.2 hz) hold

end PoincareConjecture.M47
