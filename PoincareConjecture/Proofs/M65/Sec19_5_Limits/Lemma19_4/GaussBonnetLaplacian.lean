import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetMinimalDiskPotential
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Complex InnerProductSpace
open scoped Topology ContDiff Laplacian

namespace PoincareConjecture.M65Gauss

theorem laplacian_eq_plane_trace {f : LoopPlane → ℝ} {x : LoopPlane}
    (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = ∑ i : Fin 2, fderiv ℝ (fun y =>
      fderiv ℝ f y (EuclideanSpace.basisFun (Fin 2) ℝ i)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 2) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero,
    zero_add, ContinuousLinearMap.flip_apply]

theorem laplacian_complex_parameter (f : LoopPlane → ℝ) (z : ℂ) :
    Δ (f ∘ orthonormalBasisOneI.repr) z = Δ f (orthonormalBasisOneI.repr z) := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  have he1 : e 1 = EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i
    fin_cases i <;> simp [e, orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have heI : e I = EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [e, orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have h := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (Set.mem_univ (e z)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  rw [laplacian_eq_iteratedFDeriv_complexPlane,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 2) ℝ)]
  change (iteratedFDeriv ℝ 2 (f ∘ e) z) ![1, 1] +
    (iteratedFDeriv ℝ 2 (f ∘ e) z) ![I, I] = _
  rw [h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, Fin.sum_univ_two]
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> simp [he1, heI]

theorem harmonicAt_log_distance {x a : LoopPlane} (hxa : x ≠ a) :
    HarmonicAt (fun y : LoopPlane => Real.log ‖y - a‖) x := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let f := fun y : LoopPlane => Real.log ‖y - a‖
  have hc : HarmonicAt (fun z : ℂ => Real.log ‖z - e.symm a‖) (e.symm x) :=
    (analyticAt_id.sub analyticAt_const).harmonicAt_log_norm
      (sub_ne_zero.mpr (fun h => hxa (e.symm.injective h)))
  have heq : f ∘ e = fun z : ℂ => Real.log ‖z - e.symm a‖ := by
    funext z
    change Real.log ‖e z - a‖ = Real.log ‖z - e.symm a‖
    congr 1
    have h := orthonormalBasisOneI.repr.norm_map (z - e.symm a)
    change ‖e (z - e.symm a)‖ = ‖z - e.symm a‖ at h
    simpa only [map_sub, e.apply_symm_apply] using h
  constructor
  · have hs : ContDiffAt ℝ 2 (fun y : LoopPlane => y - a) x :=
      contDiffAt_id.sub contDiffAt_const
    exact (hs.norm ℝ (sub_ne_zero.mpr hxa)).log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa))
  · have ht : ∀ᶠ y in 𝓝 x,
        Δ (fun z : ℂ => Real.log ‖z - e.symm a‖) (e.symm y) = 0 :=
      e.symm.continuous.continuousAt.eventually hc.2
    filter_upwards [ht] with y hy
    have hh := laplacian_complex_parameter f (e.symm y)
    change Δ (f ∘ e) (e.symm y) = Δ f (e (e.symm y)) at hh
    rw [heq, e.apply_symm_apply] at hh
    exact hh.symm.trans hy

private theorem harmonicAt_branch_sum {ι : Type*} (B : Finset ι)
    (a : ι → LoopPlane) (m : ι → ℝ)
    {x : LoopPlane} (hx : ∀ i ∈ B, x ≠ a i) :
    HarmonicAt (fun y => ∑ i ∈ B, m i * Real.log ‖y - a i‖) x := by
  classical
  induction B using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (harmonicAt_const (x := x) (0 : ℝ))
  | @insert i B hi ih =>
    have hxi : x ≠ a i := hx i (Finset.mem_insert_self i B)
    have hxb : ∀ j ∈ B, x ≠ a j := fun j hj => hx j (Finset.mem_insert_of_mem hj)
    have hh := (harmonicAt_log_distance hxi).const_smul (c := m i)
    have hs := hh.add (ih hxb)
    change HarmonicAt (fun y => m i * Real.log ‖y - a i‖ +
      ∑ j ∈ B, m j * Real.log ‖y - a j‖) x at hs
    simpa only [Finset.sum_insert hi] using hs

theorem logarithmic_residual_laplacian {ι : Type*} (B : Finset ι)
    (a : ι → LoopPlane) (m : ι → ℝ)
    {f u : LoopPlane → ℝ} {x : LoopPlane} {c : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hx : ∀ i ∈ B, x ≠ a i)
    (heq : u =ᶠ[𝓝 x] fun y => c * f y - ∑ i ∈ B, m i * Real.log ‖y - a i‖) :
    Δ u x = c * Δ f x := by
  have hsum := harmonicAt_branch_sum B a m hx
  have hh := (laplacian_congr_nhds heq).self_of_nhds
  have hsub := (hf.const_smul c).laplacian_sub hsum.1
  change Δ (fun y => c * f y - ∑ i ∈ B, m i * Real.log ‖y - a i‖) x =
    Δ (fun y => c * f y) x - Δ (fun y => ∑ i ∈ B, m i * Real.log ‖y - a i‖) x at hsub
  have hmul := laplacian_smul c hf
  change Δ (fun y => c * f y) x = c * Δ f x at hmul
  rw [hsub, hmul, hsum.2.self_of_nhds, Pi.zero_apply, sub_zero] at hh
  exact hh

end PoincareConjecture.M65Gauss
