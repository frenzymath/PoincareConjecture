import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapRecovery

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev
open Weak Euclidean BoundaryTangential NirenbergEuclidean

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => halfSpace 2

theorem normalDerivative_memWkp_add_two_of_weak_equation
    (k : ℕ) (B : SmoothEllipticBilinearForm 2 univ)
    {W V : Set Plane} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f v : Plane → ℝ} (hu : MemWkp (k + 2) 2 u (W ∩ Half))
    (hf : MemWkp (k + 1) 2 f (W ∩ Half)) (hvc : Continuous v)
    (hzero : ∀ z ∈ W, z 0 = 0 → v z = 0)
    (hv : v =ᵐ[volume.restrict (W ∩ Half)] chosenWeakPartial' 2 0 u (W ∩ Half))
    (heq : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ W ∩ Half →
      (∫ z in W ∩ Half, ∑ i, ∑ j,
        B.a z i j * chosenWeakPartial' 2 j u (W ∩ Half) z *
          fderiv ℝ phi z (EuclideanSpace.single i 1)) =
        ∫ z in W ∩ Half, f z * phi z) :
    MemWkp (k + 2) 2 v (V ∩ Half) := by
  have hWH : IsOpen (W ∩ Half) := hW.inter isOpen_halfSpace
  have hWHc : IsCompact (closure (W ∩ Half)) :=
    hWc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hv1 : MemW1p 2 v (W ∩ Half) :=
    (MemW1p_congr_ae hWH hv).mpr (hu.chosenWeakPartial_mem 0).memW1p
  obtain ⟨F, hF, hFeq⟩ := BoundaryNormal.exists_weak_divergence_chosenWeakPartial_sobolev
    k B hWH hWHc hu hf heq 0
  apply local_memWkp_add_two_of_continuous_zero_trace k B hW hWc hV hVc hVW
    hvc hzero hv1 hF
  intro phi hphi hpc hps
  rw [← hFeq phi hphi hpc hps]
  apply integral_congr_ae
  have hp (i : Fin 2) := chosenWeakPartial'_ae_congr (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hWH hv i
  filter_upwards [eventually_all.mpr hp] with z hz
  simp only [hz]

theorem local_neumann_memWkp_add_three
    (k : ℕ) {W V : Set Plane} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f v : Plane → ℝ} (hu : MemWkp (k + 2) 2 u (W ∩ Half))
    (hus : ContDiffOn ℝ 1 u (W ∩ Half)) (hf : MemWkp (k + 1) 2 f (W ∩ Half))
    (hvc : Continuous v) (hzero : ∀ z ∈ W, z 0 = 0 → v z = 0)
    (hv : ∀ z ∈ W ∩ Half, v z = fderiv ℝ u z (EuclideanSpace.single 0 1))
    (heq : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ W ∩ Half →
      (∫ z in W ∩ Half, ∑ i, chosenWeakPartial' 2 i u (W ∩ Half) z *
        fderiv ℝ phi z (EuclideanSpace.single i 1)) =
          ∫ z in W ∩ Half, f z * phi z) :
    MemWkp (k + 3) 2 u (V ∩ Half) := by
  have hWH : IsOpen (W ∩ Half) := hW.inter isOpen_halfSpace
  have hVH : IsOpen (V ∩ Half) := hV.inter isOpen_halfSpace
  have hsub : V ∩ Half ⊆ W ∩ Half :=
    inter_subset_inter_left _ (subset_closure.trans hVW)
  have heqB : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ W ∩ Half →
      (∫ z in W ∩ Half, ∑ i, ∑ j,
        flatBoundaryForm.a z i j * chosenWeakPartial' 2 j u (W ∩ Half) z *
          fderiv ℝ phi z (EuclideanSpace.single i 1)) =
          ∫ z in W ∩ Half, f z * phi z := by
    intro phi hphi hc hs
    simpa [flatBoundaryForm, Matrix.one_apply] using heq phi hphi hc hs
  have hnormal : v =ᵐ[volume.restrict (W ∩ Half)] chosenWeakPartial' 2 0 u (W ∩ Half) := by
    have hc := m64WeakPartial_eq_fderiv_of_contDiffOn hWH hus
      (chosenWeakPartial'_memLp_of_mem hu.memW1p 0)
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p 0)
    filter_upwards [hc, ae_restrict_mem hWH.measurableSet] with z hz hzW
    exact (hv z hzW).trans hz.symm
  have hvreg : MemWkp (k + 2) 2 v (V ∩ Half) :=
    normalDerivative_memWkp_add_two_of_weak_equation k flatBoundaryForm hW hWc hV hVc hVW
      hu hf hvc hzero hnormal heqB
  have huV : MemWkp 2 2 u (V ∩ Half) :=
    (hu.le_of_le (by omega : 2 ≤ k + 2)).mono_set (by norm_num) hVH hsub
  have hn : chosenWeakPartial' 2 0 u (V ∩ Half) =ᵐ[volume.restrict (V ∩ Half)] v := by
    have hc := m64WeakPartial_eq_fderiv_of_contDiffOn hVH (hus.mono hsub)
      (chosenWeakPartial'_memLp_of_mem huV.memW1p 0)
      (chosenWeakPartial'_isWeakPartial_of_mem huV.memW1p 0)
    filter_upwards [hc, ae_restrict_mem hVH.measurableSet] with z hz hzV
    exact hz.trans (hv z (hsub hzV)).symm
  apply planar_memWkp_add_two_of_normalDerivative (k + 1) hVH huV
    (hf.mono_set (by norm_num) hVH hsub)
    ((MemWkp_congr_ae (by norm_num) hVH hn).mpr hvreg)
  intro phi hphi hc hs
  have hraw := Poincare.Analysis.Elliptic.weakEquation_congr_restrict hsub
    (a := flatBoundaryForm.a) (q := fun j => chosenWeakPartial' 2 j u (W ∩ Half))
    (fun _ _ => rfl) (fun _ _ _ => rfl) heqB phi hphi hc hs
  simp only [flatBoundaryForm, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at hraw
  rw [← hraw]
  apply integral_congr_ae
  have hp (i : Fin 2) := chosenWeakPartial'_mono_set_ae
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hVH hsub hu.memW1p i
  filter_upwards [eventually_all.mpr hp] with z hz
  simp only [hz]

end PoincareConjecture.M64.RampTransport
