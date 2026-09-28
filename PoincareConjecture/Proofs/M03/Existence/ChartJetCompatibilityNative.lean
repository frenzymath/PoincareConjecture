import PoincareConjecture.Proofs.M03.Existence.ChartJetSource
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false

noncomputable section

open scoped ContDiff Topology

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

theorem coordinateMetricJet_second_spatial_comm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : Fin n → V) (G : V → Matrix (Fin n) (Fin n) ℝ)
    {U : Set V} (hU : IsOpen U)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun y => G y i j) U)
    {y : V} (hy : y ∈ U) (a b i j : Fin n) :
    (coordinateMetricJet e G y).second a b i j =
      (coordinateMetricJet e G y).second b a i j := by
  have hf : ContDiffAt ℝ ∞ (fun z => G z i j) y :=
    ((hG i j) y hy).contDiffAt (hU.mem_nhds hy)
  have hs : IsSymmSndFDerivAt ℝ (fun z => G z i j) y :=
    hf.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have heq := hs.eq (e a) (e b)
  have hfd : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (fun w => G w i j) z) y :=
    ((hG i j).fderiv_of_isOpen hU (by norm_num)) y hy |>.contDiffAt
      (hU.mem_nhds hy)
  have hfd_apply (c : Fin n) :
      fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z (e c)) y =
        (fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z) y).flip (e c) := by
    rw [fderiv_clm_apply (hfd.differentiableAt (by norm_num)) (by fun_prop)]
    simp
  have hleft := congrArg (fun L : V →L[ℝ] ℝ => L (e a)) (hfd_apply b)
  have hright := congrArg (fun L : V →L[ℝ] ℝ => L (e b)) (hfd_apply a)
  calc
    (coordinateMetricJet e G y).second a b i j =
        ((fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z) y) (e a)) (e b) := by
      simpa only [coordinateMetricJet, ContinuousLinearMap.flip_apply] using hleft
    _ = ((fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z) y) (e b)) (e a) := heq
    _ = (coordinateMetricJet e G y).second b a i j := by
      symm
      simpa only [coordinateMetricJet, ContinuousLinearMap.flip_apply] using hright

theorem coordinateMetricJet_second_metric_symm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : Fin n → V) (G : V → Matrix (Fin n) (Fin n) ℝ)
    {U : Set V} (hU : IsOpen U)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun y => G y i j) U)
    (hmetric : ∀ y ∈ U, ∀ i j, G y i j = G y j i)
    {y : V} (hy : y ∈ U) (a b i j : Fin n) :
    (coordinateMetricJet e G y).second a b i j =
      (coordinateMetricJet e G y).second a b j i := by
  have hEq : (fun z => G z i j) =ᶠ[𝓝 y] (fun z => G z j i) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact hmetric z hz i j
  have hfirst :
      (fun z => fderiv ℝ (fun w => G w i j) z) =ᶠ[𝓝 y]
        (fun z => fderiv ℝ (fun w => G w j i) z) :=
    hEq.fderiv
  have hsecond :
      fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z) y =
        fderiv ℝ (fun z => fderiv ℝ (fun w => G w j i) z) y :=
    hfirst.fderiv_eq
  have hsecond_eval := congrArg
    (fun L : V →L[ℝ] V →L[ℝ] ℝ => L (e a) (e b)) hsecond
  have hfdij : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (fun w => G w i j) z) y :=
    ((hG i j).fderiv_of_isOpen hU (by norm_num)) y hy |>.contDiffAt
      (hU.mem_nhds hy)
  have hfdji : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (fun w => G w j i) z) y :=
    ((hG j i).fderiv_of_isOpen hU (by norm_num)) y hy |>.contDiffAt
      (hU.mem_nhds hy)
  have hEvalij (c : Fin n) :
      fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z (e c)) y =
        (fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z) y).flip (e c) := by
    rw [fderiv_clm_apply (hfdij.differentiableAt (by norm_num)) (by fun_prop)]
    simp
  have hEvalji (c : Fin n) :
      fderiv ℝ (fun z => fderiv ℝ (fun w => G w j i) z (e c)) y =
        (fderiv ℝ (fun z => fderiv ℝ (fun w => G w j i) z) y).flip (e c) := by
    rw [fderiv_clm_apply (hfdji.differentiableAt (by norm_num)) (by fun_prop)]
    simp
  have hleft := congrArg (fun L : V →L[ℝ] ℝ => L (e a)) (hEvalij b)
  have hright := congrArg (fun L : V →L[ℝ] ℝ => L (e a)) (hEvalji b)
  calc
    (coordinateMetricJet e G y).second a b i j =
        ((fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z) y) (e a)) (e b) := by
      simpa only [coordinateMetricJet, ContinuousLinearMap.flip_apply] using hleft
    _ = ((fderiv ℝ (fun z => fderiv ℝ (fun w => G w j i) z) y) (e a)) (e b) := hsecond_eval
    _ = (coordinateMetricJet e G y).second a b j i := by
      symm
      simpa only [coordinateMetricJet, ContinuousLinearMap.flip_apply] using hright

end PoincareConjecture.DeTurckNative
