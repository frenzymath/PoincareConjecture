import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapHessian
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakClassicalColumns
import PoincareConjecture.Proofs.M60.Mathlib.SecondDerivativeChain
import Mathlib.MeasureTheory.SpecificCodomains.WithLp











set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev
open Weak Euclidean WeakCompactness BoundaryLocalization BoundaryTangential EuclideanEmbedding

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => halfSpace 2





def boundaryClassicalPartial (i : Fin 2) (u : Plane → ℝ) : Plane → ℝ :=
  fun z => fderiv ℝ u z (EuclideanSpace.single i 1)





def boundaryVectorPartial {n : ℕ} (i : Fin 2)
    (u : Plane → EuclideanSpace ℝ (Fin n)) : Plane → EuclideanSpace ℝ (Fin n) :=
  fun z => fderiv ℝ u z (EuclideanSpace.single i 1)





theorem hasWeakPartial_boundaryClassicalPartial
    {O : Set Plane} (hO : IsOpen O) {u : Plane → ℝ}
    (hu : ContDiffOn ℝ 1 u O) (i : Fin 2) :
    HasWeakPartialDeriv i (boundaryClassicalPartial i u) u O := by
  intro phi hp hc hs
  have h := setIntegral_test_fderiv hO hu hp hc hs (EuclideanSpace.single i 1)
  simp only [smul_eq_mul, mul_comm (fderiv ℝ phi _ _)] at h
  have heq : (∫ z in O, phi z * fderiv ℝ u z (EuclideanSpace.single i 1)) =
      ∫ z in O, boundaryClassicalPartial i u z * phi z := by
    apply integral_congr_ae
    exact Eventually.of_forall fun z => mul_comm _ _
  rw [heq] at h
  linarith





theorem memWkp_succ_of_boundaryClassicalPartial
    (k : ℕ) {O : Set Plane} (hO : IsOpen O) {u : Plane → ℝ}
    (hs : ContDiffOn ℝ 1 u O) (hu : MemLp u 2 (volume.restrict O))
    (hd : ∀ i, MemWkp k 2 (boundaryClassicalPartial i u) O) :
    MemWkp (k + 1) 2 u O := by
  have hw : MemW1p 2 u O :=
    ⟨hu, fun i => ⟨boundaryClassicalPartial i u, (hd i).memLp,
      hasWeakPartial_boundaryClassicalPartial hO hs i⟩⟩
  refine ⟨hw, fun i => ?_⟩
  have hae := m64WeakPartial_eq_fderiv_of_contDiffOn hO hs
    (chosenWeakPartial'_memLp_of_mem hw i) (chosenWeakPartial'_isWeakPartial_of_mem hw i)
  exact (MemWkp_congr_ae (by norm_num) hO hae).mpr (hd i)





theorem boundaryClassicalPartial_memWkp
    (k : ℕ) {O : Set Plane} (hO : IsOpen O) {u : Plane → ℝ}
    (hs : ContDiffOn ℝ 1 u O) (hu : MemWkp (k + 1) 2 u O) (i : Fin 2) :
    MemWkp k 2 (boundaryClassicalPartial i u) O := by
  have hae := m64WeakPartial_eq_fderiv_of_contDiffOn hO hs
    (chosenWeakPartial'_memLp_of_mem hu.memW1p i)
    (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
  exact (MemWkp_congr_ae (by norm_num) hO hae).mp (hu.chosenWeakPartial_mem i)





theorem memWkp_two_of_classical_hessian
    {O : Set Plane} (hO : IsOpen O) {u : Plane → ℝ}
    (hs : ContDiffOn ℝ ∞ u O) (hu : MemLp u 2 (volume.restrict O))
    (hd : ∀ i, MemLp (boundaryClassicalPartial i u) 2 (volume.restrict O))
    (hdd : ∀ i j, MemLp (boundaryClassicalPartial j (boundaryClassicalPartial i u))
      2 (volume.restrict O)) : MemWkp 2 2 u O := by
  apply memWkp_succ_of_boundaryClassicalPartial 1 hO (hs.of_le (by simp)) hu
  intro i
  apply memWkp_succ_of_boundaryClassicalPartial 0 hO
    ((hs.fderiv_of_isOpen hO (m := 1)
      (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffOn_const)
    (hd i)
  exact hdd i





theorem boundaryClassicalPartial_coordinate {n : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin n)} {z : Plane}
    (hu : DifferentiableAt ℝ u z) (i : Fin 2) (j : Fin n) :
    boundaryClassicalPartial i (fun p => u p j) z =
      (fderiv ℝ u z (EuclideanSpace.single i 1)) j := by
  let P := EuclideanSpace.proj (𝕜 := ℝ) j
  change fderiv ℝ (P ∘ u) z (EuclideanSpace.single i 1) = _
  rw [fderiv_comp z P.differentiableAt hu, P.fderiv]
  rfl






theorem boundaryVectorPartial_coordinate_memWkp {n : ℕ}
    (k : ℕ) {O : Set Plane} (hO : IsOpen O)
    {u : Plane → EuclideanSpace ℝ (Fin n)} (hs : ContDiffOn ℝ 1 u O)
    (hu : ∀ j, MemWkp (k + 1) 2 (fun z => u z j) O) (i : Fin 2) (j : Fin n) :
    MemWkp k 2 (fun z => boundaryVectorPartial i u z j) O := by
  have hpart := boundaryClassicalPartial_memWkp k hO
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hs) (hu j) i
  apply (MemWkp_congr_ae (by norm_num) hO ?_).mp hpart
  filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
  exact boundaryClassicalPartial_coordinate
    ((hs.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) i j





theorem boundaryClassicalSecond_coordinate {n : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin n)} {z : Plane}
    (hu : ContDiffAt ℝ ∞ u z) (a b : Fin 2) (j : Fin n) :
    boundaryClassicalPartial b (boundaryClassicalPartial a (fun p => u p j)) z =
      (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single b 1)
        (EuclideanSpace.single a 1)) j := by
  have heq : boundaryClassicalPartial a (fun p => u p j) =ᶠ[𝓝 z]
      (fun p => (fderiv ℝ u p (EuclideanSpace.single a 1)) j) := by
    have hu1 : ContDiffAt ℝ 1 u z := hu.of_le (by simp)
    filter_upwards [hu1.eventually (by norm_num : (1 : ℕ∞ω) ≠ (∞ : ℕ∞ω))] with p hp
    exact boundaryClassicalPartial_coordinate (hp.differentiableAt (by simp)) a j
  have hs : ContDiffAt ℝ 1 (fun p => fderiv ℝ u p (EuclideanSpace.single a 1)) z :=
    (hu.fderiv_right (m := 1)
      (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffAt_const
  change fderiv ℝ _ z (EuclideanSpace.single b 1) = _
  rw [heq.fderiv_eq]
  rw [show fderiv ℝ (fun p => (fderiv ℝ u p (EuclideanSpace.single a 1)) j) z
        (EuclideanSpace.single b 1) =
      (fderiv ℝ (fun p => fderiv ℝ u p (EuclideanSpace.single a 1)) z
        (EuclideanSpace.single b 1)) j from
      boundaryClassicalPartial_coordinate (hs.differentiableAt (by simp)) b j]
  rw [M60.fderiv_column (hu.of_le (WithTop.coe_le_coe.mpr le_top))]





theorem vector_memWkp_two_of_classical_hessian {n : ℕ}
    {O : Set Plane} (hO : IsOpen O) {u : Plane → EuclideanSpace ℝ (Fin n)}
    (hs : ContDiffOn ℝ ∞ u O) (hu : MemLp u 2 (volume.restrict O))
    (hd : ∀ i : Fin 2, MemLp (fun z => fderiv ℝ u z (EuclideanSpace.single i 1))
      2 (volume.restrict O))
    (hdd : ∀ i j : Fin 2, MemLp (fun z => fderiv ℝ (fderiv ℝ u) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) 2 (volume.restrict O)) :
    ∀ j : Fin n, MemWkp 2 2 (fun z => u z j) O := by
  intro j
  apply memWkp_two_of_classical_hessian hO
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hs) (hu.eval_piLp j)
  · intro i
    apply MemLp.ae_eq ?_ ((hd i).eval_piLp j)
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    exact (boundaryClassicalPartial_coordinate
      ((hs.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) i j).symm
  · intro a b
    apply MemLp.ae_eq ?_ ((hdd b a).eval_piLp j)
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    exact (boundaryClassicalSecond_coordinate (hs.contDiffAt (hO.mem_nhds hz)) a b j).symm





theorem hessian_memLp_of_coordinate_memWkp_two {n : ℕ}
    {O : Set Plane} (hO : IsOpen O) {u : Plane → EuclideanSpace ℝ (Fin n)}
    (hs : ContDiffOn ℝ ∞ u O) (hu : ∀ j, MemWkp 2 2 (fun z => u z j) O)
    (a b : Fin 2) :
    MemLp (fun z => fderiv ℝ (fderiv ℝ u) z
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) 2 (volume.restrict O) := by
  have hVs : ContDiffOn ℝ ∞ (boundaryVectorPartial b u) O :=
    (hs.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hV (j : Fin n) : MemWkp 1 2 (fun z => boundaryVectorPartial b u z j) O :=
    boundaryVectorPartial_coordinate_memWkp 1 hO (hs.of_le (by simp)) hu b j
  have hW : MemLp (boundaryVectorPartial a (boundaryVectorPartial b u))
      2 (volume.restrict O) := by
    apply MemLp.of_eval_piLp
    intro j
    exact boundaryVectorPartial_coordinate_memWkp 0 hO (hVs.of_le (by simp)) hV a j
  apply MemLp.ae_eq ?_ hW
  filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
  exact M60.fderiv_column
    ((hs.contDiffAt (hO.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top))
    (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)






theorem compact_halfSpace_H1_memLp_four {u : Plane → ℝ}
    (hc : HasCompactSupport u) (hu : MemWkp 1 2 u Half) :
    MemLp u 4 (volume.restrict Half) := by
  have hup : MemWkp 1 (ENNReal.ofReal (4 / 3)) u Half :=
    EuclideanIteratedMonoExp.memWkp_mono_exponent_of_tsupport_subset 1
      isOpen_halfSpace (isClosed_tsupport u) hc.measure_lt_top.ne
      (by norm_num) (by norm_num) (subset_refl _) hu
  have h : MemWkp 0 4 u Half := by
    convert! BoundaryEmbedding.memWkp_subcritical 0
      (by norm_num : (1 : ℝ) ≤ 4 / 3) (by norm_num : (4 / 3 : ℝ) < 2) hc hup using 1
    norm_num
  exact h





theorem local_halfSpace_H1_memLp_four
    {W V : Set Plane} (hW : IsOpen W) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u : Plane → ℝ} (hu : MemWkp 1 2 u (W ∩ Half)) :
    MemLp u 4 (volume.restrict (V ∩ Half)) := by
  obtain ⟨chi, hchi, hc, _, hone, hs⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hVc hW hVW
  have hcut : MemWkp 1 2 (fun z => chi z * u z) Half :=
    memWkp_mul_smooth_of_tsupport_subset 1 isOpen_halfSpace hW hu hchi hc hs
  have hLp := (compact_halfSpace_H1_memLp_four hc.mul_right hcut).mono_measure
    (Measure.restrict_mono_set volume (inter_subset_right : V ∩ Half ⊆ Half))
  apply MemLp.ae_eq ?_ hLp
  filter_upwards [ae_restrict_mem (hV.inter isOpen_halfSpace).measurableSet] with z hz
  change chi z * u z = u z
  rw [hone z (subset_closure hz.1), one_mul]





theorem local_H3_classical_hessian_memLp_four
    {W V : Set Plane} (hW : IsOpen W) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u : Plane → ℝ} (hs : ContDiffOn ℝ ∞ u (W ∩ Half))
    (hu : MemWkp 3 2 u (W ∩ Half)) (i j : Fin 2) :
    MemLp (boundaryClassicalPartial j (boundaryClassicalPartial i u))
      4 (volume.restrict (V ∩ Half)) := by
  have hWH : IsOpen (W ∩ Half) := hW.inter isOpen_halfSpace
  apply local_halfSpace_H1_memLp_four hW hV hVc hVW
  apply boundaryClassicalPartial_memWkp 1 hWH
    ((hs.fderiv_of_isOpen hWH (m := 1)
      (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffOn_const)
  exact boundaryClassicalPartial_memWkp 2 hWH (hs.of_le (by simp)) hu i





theorem H3_classical_third_memLp_two
    {O : Set Plane} (hO : IsOpen O) {u : Plane → ℝ}
    (hs : ContDiffOn ℝ ∞ u O) (hu : MemWkp 3 2 u O) (i j k : Fin 2) :
    MemLp (boundaryClassicalPartial k
      (boundaryClassicalPartial j (boundaryClassicalPartial i u)))
      2 (volume.restrict O) := by
  have hi : ContDiffOn ℝ ∞ (boundaryClassicalPartial i u) O :=
    (hs.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hj : ContDiffOn ℝ ∞ (boundaryClassicalPartial j (boundaryClassicalPartial i u)) O :=
    (hi.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  exact boundaryClassicalPartial_memWkp 0 hO (hj.of_le (by simp))
    (boundaryClassicalPartial_memWkp 1 hO (hi.of_le (by simp))
      (boundaryClassicalPartial_memWkp 2 hO (hs.of_le (by simp)) hu i) j) k

end PoincareConjecture.M64.RampTransport
