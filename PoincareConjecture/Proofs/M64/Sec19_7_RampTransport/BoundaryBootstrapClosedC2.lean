import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapHessian
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryClassicalGradient
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakClassicalColumns
import Mathlib.Analysis.Calculus.ContDiff.WithLp












set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev
open Weak Euclidean BoundaryTangential
open M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => halfSpace 2

private theorem contDiffOn_one_of_continuous_derivative
    {f : Plane → ℝ} {K : Set Plane} {J : Plane → Plane →L[ℝ] ℝ}
    (hJ : Continuous J) (hd : ∀ x ∈ K, HasFDerivWithinAt f (J x) K x) :
    ContDiffOn ℝ 1 f K := by
  change ContDiffOn ℝ ((0 : ℕ∞ω) + 1) f K
  rw [contDiffOn_succ_iff_hasFDerivWithinAt (by norm_num : (0 : ℕ∞ω) ≠ (∞ : ℕ∞ω))]
  intro x hx
  refine ⟨K, ?_, ?_, J, hd, contDiffOn_zero.mpr hJ.continuousOn⟩
  · rw [insert_eq_of_mem hx]
    exact self_mem_nhdsWithin
  · intro h
    norm_num at h






theorem compact_halfSpace_H4_contDiffOn_closure
    {u U : Plane → ℝ} (hc : HasCompactSupport u) (hu : MemWkp 4 2 u Half)
    {O : Set Plane} (hO : IsOpen O) (hconv : Convex ℝ O) (hOH : O ⊆ Half)
    (hUs : ContDiffOn ℝ ∞ U O) (hU : U =ᵐ[volume.restrict O] u)
    (hUc : ContinuousOn U (closure O)) :
    ContDiffOn ℝ 2 U (closure O) := by
  obtain ⟨G, hGc, hG⟩ := scalar_halfSpace_H3_continuous_gradient hc hu.le_succ
  let v (i : Fin 2) := iteratedZeroExtension 2 Half (tsupport u) 1 (fun _ : Fin 1 => i) u
  have hvc (i : Fin 2) : HasCompactSupport (v i) :=
    hasCompactSupport_iteratedZeroExtension hc (isClosed_tsupport u) (subset_refl _) 1 _
  have hv (i : Fin 2) : MemWkp 3 2 (v i) Half := by
    simpa only [v] using iteratedZeroExtension_memWkp
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) isOpen_halfSpace (isClosed_tsupport u)
      1 4 (by omega) (fun _ : Fin 1 => i) hu (subset_refl _)
  have hvae (i : Fin 2) : v i =ᵐ[volume.restrict Half] chosenWeakPartial' 2 i u Half := by
    have h := iteratedZeroExtension_ae_eq_iterWeakPartial
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) isOpen_halfSpace (isClosed_tsupport u)
      1 4 (by omega) (fun _ : Fin 1 => i) hu (subset_refl _)
    simpa only [v, iterWeakPartial_succ, iterWeakPartial_zero] using h
  have hpart (i : Fin 2) : EqOn (G i)
      (fun x => fderiv ℝ U x (EuclideanSpace.single i 1)) O := by
    have hp : MemLp (chosenWeakPartial' 2 i u Half) 2 (volume.restrict O) :=
      (chosenWeakPartial'_memLp_of_mem hu.memW1p i).mono_measure
        (Measure.restrict_mono_set volume hOH)
    have hw : HasWeakPartialDeriv i (chosenWeakPartial' 2 i u Half) U O :=
      hasWeakPartialDeriv_congr_ae hO i hU.symm
        ((chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i).restrict hO hOH)
    have hclass := m64WeakPartial_eq_fderiv_of_contDiffOn hO
      (hUs.of_le (by simp)) hp hw
    have hae : G i =ᵐ[volume.restrict O]
        (fun x => fderiv ℝ U x (EuclideanSpace.single i 1)) := by
      have hg : chosenWeakPartial' 2 i u Half =ᵐ[volume.restrict O] G i :=
        ae_restrict_of_ae_restrict_of_subset hOH (hG i)
      exact hg.symm.trans hclass
    apply Measure.eqOn_open_of_ae_eq hae hO (hGc i).continuousOn
    exact (hUs.continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
  have hGs (i : Fin 2) : ContDiffOn ℝ ∞ (G i) O :=
    ((hUs.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const).congr (hpart i)
  have hGv (i : Fin 2) : G i =ᵐ[volume.restrict O] v i :=
    ae_restrict_of_ae_restrict_of_subset hOH ((hvae i).trans (hG i)).symm
  have hG1 (i : Fin 2) : ContDiffOn ℝ 1 (G i) (closure O) := by
    obtain ⟨J, hJ, _, hd⟩ := scalar_halfSpace_H3_boundary_derivative
      (hvc i) (hv i) hO hconv hOH (hGs i) (hGv i) (hGc i).continuousOn
    exact contDiffOn_one_of_continuous_derivative hJ (fun x _ => hd x)
  let D : Plane → Plane →L[ℝ] ℝ := fun x => M60.suPlaneColumns (fun i => G i x)
  have hDc : Continuous D := by
    have h (i : Fin 2) :=
      (ContinuousLinearMap.smulRightL ℝ Plane ℝ (EuclideanSpace.proj i)).continuous.comp (hGc i)
    exact (h 0).add (h 1)
  have hD1 : ContDiffOn ℝ 1 D (closure O) := by
    have h (i : Fin 2) :=
      (ContinuousLinearMap.smulRightL ℝ Plane ℝ (EuclideanSpace.proj i)).contDiff.comp_contDiffOn
        (hG1 i)
    exact (h 0).add (h 1)
  have hDu : EqOn D (fderiv ℝ U) O := by
    intro x hx
    rw [← M60.suPlaneColumns_reconstruct (fderiv ℝ U x)]
    exact congrArg M60.suPlaneColumns (funext fun i => hpart i hx)
  obtain ⟨J, hJ, hUJ, hd⟩ := scalar_halfSpace_H3_boundary_derivative
    hc hu.le_succ hO hconv hOH hUs hU hUc
  have hDJ : EqOn D J (closure O) := (hDu.trans hUJ).closure hDc hJ
  change ContDiffOn ℝ ((1 : ℕ∞ω) + 1) U (closure O)
  rw [contDiffOn_succ_iff_hasFDerivWithinAt (by norm_num : (1 : ℕ∞ω) ≠ (∞ : ℕ∞ω))]
  intro x hx
  refine ⟨closure O, ?_, ?_, D, ?_, hD1⟩
  · rw [insert_eq_of_mem hx]
    exact self_mem_nhdsWithin
  · intro h
    norm_num at h
  · intro y hy
    rw [hDJ hy]
    exact hd y





theorem compact_halfSpace_H4_vector_contDiffOn_closure
    {n : ℕ} {u U : Plane → EuclideanSpace ℝ (Fin n)}
    (hc : ∀ i, HasCompactSupport (fun z => u z i))
    (hu : ∀ i, MemWkp 4 2 (fun z => u z i) Half)
    {O : Set Plane} (hO : IsOpen O) (hconv : Convex ℝ O) (hOH : O ⊆ Half)
    (hUs : ContDiffOn ℝ ∞ U O) (hU : U =ᵐ[volume.restrict O] u)
    (hUc : ContinuousOn U (closure O)) :
    ContDiffOn ℝ 2 U (closure O) := by
  apply contDiffOn_piLp'
  intro i
  apply compact_halfSpace_H4_contDiffOn_closure (hc i) (hu i) hO hconv hOH
    ((EuclideanSpace.proj i).contDiff.comp_contDiffOn hUs)
  · filter_upwards [hU] with z hz
    exact congrArg (fun y => y i) hz
  · exact (EuclideanSpace.proj i).continuous.comp_continuousOn hUc






theorem local_halfSpace_H4_contDiffOn_closure
    {W O : Set Plane} (hW : IsOpen W) (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hconv : Convex ℝ O)
    (hOH : O ⊆ Half) (hOW : closure O ⊆ W)
    {u : Plane → ℝ} (hu : MemWkp 4 2 u (W ∩ Half))
    (hs : ContDiffOn ℝ ∞ u O) (hc : ContinuousOn u (closure O)) :
    ContDiffOn ℝ 2 u (closure O) := by
  obtain ⟨chi, hchi, hchic, _, hone, hsupp⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hOc hW hOW
  have hcut : MemWkp 4 2 (fun z => chi z * u z) Half :=
    BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset 4
      isOpen_halfSpace hW hu hchi hchic hsupp
  apply compact_halfSpace_H4_contDiffOn_closure hchic.mul_right hcut hO hconv hOH hs
  · filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    change u z = chi z * u z
    rw [hone z (subset_closure hz), one_mul]
  · exact hc





theorem local_halfSpace_H4_vector_contDiffOn_closure
    {n : ℕ} {W O : Set Plane} (hW : IsOpen W) (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hconv : Convex ℝ O)
    (hOH : O ⊆ Half) (hOW : closure O ⊆ W)
    {u : Plane → EuclideanSpace ℝ (Fin n)}
    (hu : ∀ i, MemWkp 4 2 (fun z => u z i) (W ∩ Half))
    (hs : ContDiffOn ℝ ∞ u O) (hc : ContinuousOn u (closure O)) :
    ContDiffOn ℝ 2 u (closure O) := by
  apply contDiffOn_piLp'
  intro i
  exact local_halfSpace_H4_contDiffOn_closure hW hO hOc hconv hOH hOW (hu i)
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hs)
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hc)

end PoincareConjecture.M64.RampTransport
