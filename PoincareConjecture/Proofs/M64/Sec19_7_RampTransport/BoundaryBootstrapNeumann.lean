import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryZeroExtension
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryZeroTraceApproximation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakClassicalColumns
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Regularity.Tangential

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev
open Weak Euclidean BoundaryTangential NirenbergEuclidean BoundaryLocalization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => halfSpace 2

private theorem zeroExtension_memW01p_of_continuous
    {u : Plane → ℝ} (huc : Continuous u) (hc : HasCompactSupport u)
    (hzero : ∀ z : Plane, z 0 = 0 → u z = 0) (hu : MemW1p 2 u Half) :
    MemW01p 2 ((Half).indicator u) Half := by
  have hLp : MemLp ((Half).indicator u) 2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu.1
  have hp (i : Fin 2) : MemLp ((Half).indicator (chosenWeakPartial' 2 i u Half))
      2 volume :=
    (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr
      (chosenWeakPartial'_memLp_of_mem hu i)
  have hw : MemW1p 2 ((Half).indicator u) univ := by
    refine ⟨by simpa only [Measure.restrict_univ] using hLp, fun i => ?_⟩
    refine ⟨(Half).indicator (chosenWeakPartial' 2 i u Half),
      by simpa only [Measure.restrict_univ] using hp i, ?_⟩
    exact m64Continuous_zeroExtension_weak i huc hzero hu.1
      (chosenWeakPartial'_memLp_of_mem hu i)
      (chosenWeakPartial'_isWeakPartial_of_mem hu i)
  have hzc : HasCompactSupport ((Half).indicator u) := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro z hz
    apply subset_tsupport u
    change u z ≠ 0
    intro huz
    by_cases hzH : z ∈ Half <;> simp [hzH, huz] at hz
  exact m64MemW01p_of_halfspace_support hw.someWitness hzc 0 (fun z hz => by
    apply indicator_of_notMem
    exact not_lt.mpr hz.le)

theorem local_memWkp_add_two_of_continuous_zero_trace
    (k : ℕ) (B : SmoothEllipticBilinearForm 2 univ)
    {W V : Set Plane} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f : Plane → ℝ} (huc : Continuous u)
    (hzero : ∀ z ∈ W, z 0 = 0 → u z = 0)
    (hu : MemW1p 2 u (W ∩ Half)) (hf : MemWkp k 2 f (W ∩ Half))
    (heq : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ W ∩ Half →
      (∫ z in W ∩ Half, ∑ i, ∑ j,
        B.a z i j * chosenWeakPartial' 2 j u (W ∩ Half) z *
          fderiv ℝ phi z (EuclideanSpace.single i 1)) =
        ∫ z in W ∩ Half, f z * phi z) :
    MemWkp (k + 2) 2 u (V ∩ Half) := by
  obtain ⟨U, hU, hVU, hUW⟩ :=
    hVc.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hVW)
  have hUc : IsCompact (closure U) :=
    hWc.of_isClosed_subset isClosed_closure (hUW.trans subset_closure)
  obtain ⟨chi, hchi, hc, _, hone, hs⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hUc hW hUW
  let w : Plane → ℝ := fun z => chi z * u z
  let zext : Plane → ℝ := (Half).indicator w
  have hwc : Continuous w := hchi.continuous.mul huc
  have hwzero (z : Plane) (hz : z 0 = 0) : w z = 0 := by
    by_cases hzchi : chi z = 0
    · simp only [w, hzchi, zero_mul]
    · rw [show w z = chi z * u z from rfl, hzero z (hs (subset_tsupport chi hzchi)) hz,
        mul_zero]
  have hw : MemW1p 2 w Half :=
    (memWkp_mul_smooth_of_tsupport_subset 1 isOpen_halfSpace hW
      (MemWkp.one_iff_memW1p.mpr hu) hchi hc hs).memW1p
  have hz0 : MemW01p 2 zext Half :=
    zeroExtension_memW01p_of_continuous hwc hc.mul_right hwzero hw
  have hUH : IsOpen (U ∩ Half) := hU.inter isOpen_halfSpace
  have hsub : U ∩ Half ⊆ W ∩ Half :=
    inter_subset_inter_left _ (subset_closure.trans hUW)
  have hzu : zext =ᵐ[volume.restrict (U ∩ Half)] u := by
    filter_upwards [ae_restrict_mem hUH.measurableSet] with z hz
    simp only [zext, indicator_of_mem hz.2, w, hone z (subset_closure hz.1), one_mul]
  have hp (i : Fin 2) : chosenWeakPartial' 2 i zext (U ∩ Half)
      =ᵐ[volume.restrict (U ∩ Half)] chosenWeakPartial' 2 i u (W ∩ Half) :=
    (chosenWeakPartial'_ae_congr (by norm_num) hUH hzu i).trans
      (chosenWeakPartial'_mono_set_ae (by norm_num) hUH hsub hu i).symm
  have hzEq : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ U ∩ Half →
      (∫ z in U ∩ Half, ∑ i, ∑ j,
        B.a z i j * chosenWeakPartial' 2 j zext (U ∩ Half) z *
          fderiv ℝ phi z (EuclideanSpace.single i 1)) =
        ∫ z in U ∩ Half, f z * phi z := by
    intro phi hphi hpc hps
    have hraw := Poincare.Analysis.Elliptic.weakEquation_congr_restrict hsub
      (a := B.a) (q := fun j => chosenWeakPartial' 2 j u (W ∩ Half))
      (fun _ _ => rfl) (fun _ _ _ => rfl) heq phi hphi hpc hps
    simp only [Finset.sum_mul] at hraw
    rw [← hraw]
    apply integral_congr_ae
    filter_upwards [eventually_all.mpr hp] with z hz
    simp only [hz]
  have hzreg : MemWkp (k + 2) 2 zext (V ∩ Half) :=
    memWkp_add_two_of_local_weakEquation k B hU hV hVc hVU hz0
      (hf.mono_set (by norm_num) hUH hsub) hzEq
  apply (MemWkp_congr_ae (by norm_num) (hV.inter isOpen_halfSpace) (v := u) ?_).mp hzreg
  filter_upwards [ae_restrict_mem (hV.inter isOpen_halfSpace).measurableSet] with z hz
  simp only [zext, indicator_of_mem hz.2, w,
    hone z (subset_closure (hVU (subset_closure hz.1))), one_mul]

theorem normalDerivative_memWkp_two_of_weak_equation
    (B : SmoothEllipticBilinearForm 2 univ)
    {W V : Set Plane} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f v : Plane → ℝ} (hu : MemWkp 2 2 u (W ∩ Half))
    (hf : MemWkp 1 2 f (W ∩ Half)) (hvc : Continuous v)
    (hzero : ∀ z ∈ W, z 0 = 0 → v z = 0)
    (hv : v =ᵐ[volume.restrict (W ∩ Half)] chosenWeakPartial' 2 0 u (W ∩ Half))
    (heq : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ W ∩ Half →
      (∫ z in W ∩ Half, ∑ i, ∑ j,
        B.a z i j * chosenWeakPartial' 2 j u (W ∩ Half) z *
          fderiv ℝ phi z (EuclideanSpace.single i 1)) =
        ∫ z in W ∩ Half, f z * phi z) :
    MemWkp 2 2 v (V ∩ Half) := by
  have hWH : IsOpen (W ∩ Half) := hW.inter isOpen_halfSpace
  have hWHc : IsCompact (closure (W ∩ Half)) :=
    hWc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hv1 : MemW1p 2 v (W ∩ Half) :=
    (MemW1p_congr_ae hWH hv).mpr (hu.chosenWeakPartial_mem 0).memW1p
  obtain ⟨F, hF, hFeq⟩ := exists_weak_divergence_chosenWeakPartial
    hWH hWHc B.a B.smooth_a hu hf.memW1p heq 0
  apply local_memWkp_add_two_of_continuous_zero_trace 0 B hW hWc hV hVc hVW
    hvc hzero hv1 hF
  intro phi hphi hpc hps
  rw [← hFeq phi hphi hpc hps]
  apply integral_congr_ae
  have hp (i : Fin 2) := chosenWeakPartial'_ae_congr (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hWH hv i
  filter_upwards [eventually_all.mpr hp] with z hz
  simp only [hz]

theorem normalDerivative_memWkp_two
    (B : SmoothEllipticBilinearForm 2 univ)
    {W V : Set Plane} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f v : Plane → ℝ} (hu : MemWkp 2 2 u (W ∩ Half))
    (hus : ContDiffOn ℝ 1 u (W ∩ Half)) (hf : MemWkp 1 2 f (W ∩ Half))
    (hvc : Continuous v) (hzero : ∀ z ∈ W, z 0 = 0 → v z = 0)
    (hv : ∀ z ∈ W ∩ Half, v z = fderiv ℝ u z (EuclideanSpace.single 0 1))
    (heq : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ W ∩ Half →
      (∫ z in W ∩ Half, ∑ i, ∑ j,
        B.a z i j * chosenWeakPartial' 2 j u (W ∩ Half) z *
          fderiv ℝ phi z (EuclideanSpace.single i 1)) =
        ∫ z in W ∩ Half, f z * phi z) :
    MemWkp 2 2 v (V ∩ Half) := by
  have hWH : IsOpen (W ∩ Half) := hW.inter isOpen_halfSpace
  have hp := m64WeakPartial_eq_fderiv_of_contDiffOn hWH hus
    (chosenWeakPartial'_memLp_of_mem hu.memW1p 0)
    (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p 0)
  apply normalDerivative_memWkp_two_of_weak_equation B hW hWc hV hVc hVW
    hu hf hvc hzero ?_ heq
  filter_upwards [hp, ae_restrict_mem hWH.measurableSet] with z hpz hz
  exact (hv z hz).trans hpz.symm

end PoincareConjecture.M64.RampTransport
