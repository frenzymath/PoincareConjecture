import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapNeumann











set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev
open Weak Euclidean BoundaryTangential NirenbergEuclidean

local notation "Plane" => EuclideanSpace ℝ (Fin 2)





def flatBoundaryForm : SmoothEllipticBilinearForm 2 univ where
  a := fun _ => 1
  c := fun _ => 0
  symm := by intro _ i j; simp only [Matrix.one_apply, eq_comm]
  smooth_a := fun _ _ => contDiff_const
  smooth_c := contDiff_const
  lam := 1
  capLam := 1
  hlam_pos := by norm_num
  hlam_le_capLam := le_rfl
  coercive := by
    intro x hx v
    have hm : matMulE (1 : Matrix (Fin 2) (Fin 2) ℝ) v = v := by
      apply PiLp.ext
      intro i
      simp [matMulE]
    rw [hm, real_inner_self_eq_norm_sq, one_mul]






theorem planar_memWkp_add_two_of_normalDerivative
    (k : ℕ) {O : Set Plane} (hO : IsOpen O)
    {u f : Plane → ℝ} (hu : MemWkp 2 2 u O) (hf : MemWkp k 2 f O)
    (hn : MemWkp (k + 1) 2 (chosenWeakPartial' 2 0 u O) O)
    (heq : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O →
      (∫ z in O, ∑ i, chosenWeakPartial' 2 i u O z *
        fderiv ℝ phi z (EuclideanSpace.single i 1)) = ∫ z in O, f z * phi z) :
    MemWkp (k + 2) 2 u O := by
  let p (i : Fin 2) : Plane → ℝ := chosenWeakPartial' 2 i u O
  let q (i : Fin 2) : Plane → ℝ := chosenWeakPartial' 2 i (p 0) O
  have hp (i : Fin 2) : MemW1p 2 (p i) O := (hu.chosenWeakPartial_mem i).memW1p
  have hpu (i : Fin 2) : HasWeakPartialDeriv i (p i) u O :=
    chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i
  have hq (i : Fin 2) : MemWkp k 2 (q i) O := hn.chosenWeakPartial_mem i
  have hqw (i : Fin 2) : HasWeakPartialDeriv i (q i) (p 0) O :=
    chosenWeakPartial'_isWeakPartial_of_mem (hp 0) i
  have hq0p1 : HasWeakPartialDeriv 0 (q 1) (p 1) O :=
    weakPartial_commute 0 1 (hpu 0) (hpu 1) (hqw 1)
  have heq0 : chosenWeakPartial' 2 0 (p 1) O =ᵐ[volume.restrict O] q 1 :=
    HasWeakPartialDeriv.ae_eq hO
      (chosenWeakPartial'_isWeakPartial_of_mem (hp 1) 0) hq0p1
      ((chosenWeakPartial'_memLp_of_mem (hp 1) 0).locallyIntegrable (by norm_num))
      ((hq 1).memLp.locallyIntegrable (by norm_num))
  let r : Plane → ℝ := fun z => -f z - q 0 z
  have hr : MemWkp k 2 r O :=
    MemWkp.sub (by norm_num) hO (MemWkp.neg (by norm_num) hO hf) (hq 0)
  have hrw : HasWeakPartialDeriv 1 r (p 1) O := by
    intro phi hphi hc hs
    have hphi2 : MemLp phi 2 (volume.restrict O) :=
      (hphi.continuous.memLp_of_hasCompactSupport hc).restrict O
    have hdphi2 (i : Fin 2) : MemLp
        (fun z => fderiv ℝ phi z (EuclideanSpace.single i 1)) 2 (volume.restrict O) :=
      (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const
        ).memLp_of_hasCompactSupport (hc.fderiv_apply ℝ _)).restrict O
    have hpI (i : Fin 2) : Integrable
        (fun z => p i z * fderiv ℝ phi z (EuclideanSpace.single i 1))
        (volume.restrict O) := (hp i).1.integrable_mul (hdphi2 i)
    have hfI : Integrable (fun z => f z * phi z) (volume.restrict O) :=
      hf.memLp.integrable_mul hphi2
    have hqI : Integrable (fun z => q 0 z * phi z) (volume.restrict O) :=
      (hq 0).memLp.integrable_mul hphi2
    have hmain := heq phi hphi hc hs
    simp only [Fin.sum_univ_two] at hmain
    change (∫ z in O, p 0 z * fderiv ℝ phi z (EuclideanSpace.single 0 1) +
      p 1 z * fderiv ℝ phi z (EuclideanSpace.single 1 1)) = _ at hmain
    rw [integral_add (hpI 0) (hpI 1)] at hmain
    have hnormal := hqw 0 phi hphi hc hs
    have hsource : (∫ z in O, r z * phi z) =
        -(∫ z in O, f z * phi z) - ∫ z in O, q 0 z * phi z := by
      simp only [r, sub_mul, neg_mul]
      simpa only [Pi.neg_apply, integral_neg] using integral_sub hfI.neg hqI
    rw [hsource]
    linarith
  have heq1 : chosenWeakPartial' 2 1 (p 1) O =ᵐ[volume.restrict O] r :=
    HasWeakPartialDeriv.ae_eq hO
      (chosenWeakPartial'_isWeakPartial_of_mem (hp 1) 1) hrw
      ((chosenWeakPartial'_memLp_of_mem (hp 1) 1).locallyIntegrable (by norm_num))
      (hr.memLp.locallyIntegrable (by norm_num))
  have hp1 : MemWkp (k + 1) 2 (p 1) O := by
    refine ⟨hp 1, fun i => ?_⟩
    fin_cases i
    · exact (MemWkp_congr_ae (by norm_num) hO heq0).mpr (hq 1)
    · exact (MemWkp_congr_ae (by norm_num) hO heq1).mpr hr
  refine ⟨hu.memW1p, fun i => ?_⟩
  fin_cases i
  · exact hn
  · exact hp1






theorem local_neumann_memWkp_three
    {W V : Set Plane} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f v : Plane → ℝ} (hu : MemWkp 2 2 u (W ∩ halfSpace 2))
    (hus : ContDiffOn ℝ 1 u (W ∩ halfSpace 2))
    (hf : MemWkp 1 2 f (W ∩ halfSpace 2)) (hvc : Continuous v)
    (hzero : ∀ z ∈ W, z 0 = 0 → v z = 0)
    (hv : ∀ z ∈ W ∩ halfSpace 2,
      v z = fderiv ℝ u z (EuclideanSpace.single 0 1))
    (heq : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ W ∩ halfSpace 2 →
      (∫ z in W ∩ halfSpace 2, ∑ i, chosenWeakPartial' 2 i u (W ∩ halfSpace 2) z *
        fderiv ℝ phi z (EuclideanSpace.single i 1)) =
          ∫ z in W ∩ halfSpace 2, f z * phi z) :
    MemWkp 3 2 u (V ∩ halfSpace 2) := by
  have hWH : IsOpen (W ∩ halfSpace 2) := hW.inter isOpen_halfSpace
  have hVH : IsOpen (V ∩ halfSpace 2) := hV.inter isOpen_halfSpace
  have hsub : V ∩ halfSpace 2 ⊆ W ∩ halfSpace 2 :=
    inter_subset_inter_left _ (subset_closure.trans hVW)
  have heqB : ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ W ∩ halfSpace 2 →
      (∫ z in W ∩ halfSpace 2, ∑ i, ∑ j,
        flatBoundaryForm.a z i j * chosenWeakPartial' 2 j u (W ∩ halfSpace 2) z *
          fderiv ℝ phi z (EuclideanSpace.single i 1)) =
          ∫ z in W ∩ halfSpace 2, f z * phi z := by
    intro phi hphi hc hs
    simpa [flatBoundaryForm, Matrix.one_apply] using heq phi hphi hc hs
  have hv2 : MemWkp 2 2 v (V ∩ halfSpace 2) :=
    normalDerivative_memWkp_two flatBoundaryForm hW hWc hV hVc hVW
      hu hus hf hvc hzero hv heqB
  have huV : MemWkp 2 2 u (V ∩ halfSpace 2) := hu.mono_set (by norm_num) hVH hsub
  have hn : chosenWeakPartial' 2 0 u (V ∩ halfSpace 2)
      =ᵐ[volume.restrict (V ∩ halfSpace 2)] v := by
    have hc := m64WeakPartial_eq_fderiv_of_contDiffOn hVH (hus.mono hsub)
      (chosenWeakPartial'_memLp_of_mem huV.memW1p 0)
      (chosenWeakPartial'_isWeakPartial_of_mem huV.memW1p 0)
    filter_upwards [hc, ae_restrict_mem hVH.measurableSet] with z hz hzV
    exact hz.trans (hv z (hsub hzV)).symm
  apply planar_memWkp_add_two_of_normalDerivative 1 hVH huV
    (hf.mono_set (by norm_num) hVH hsub)
    ((MemWkp_congr_ae (by norm_num) hVH hn).mpr hv2)
  intro phi hphi hc hs
  have hraw := Poincare.Analysis.Elliptic.weakEquation_congr_restrict hsub
    (a := flatBoundaryForm.a) (q := fun j => chosenWeakPartial' 2 j u (W ∩ halfSpace 2))
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
