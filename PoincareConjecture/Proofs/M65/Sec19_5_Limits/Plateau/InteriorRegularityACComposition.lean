import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm











set_option autoImplicit false

open Set Metric MeasureTheory Filter
open scoped Topology NNReal

namespace PoincareConjecture.M65Interior




theorem ac_comp_lipschitz {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {v : ℝ → E} {g : E → F} {a b : ℝ} {S : Set E} {K : ℝ≥0}
    (hv : AbsolutelyContinuousOnInterval v a b) (hg : LipschitzOnWith K g S)
    (hvs : MapsTo v (uIcc a b) S) : AbsolutelyContinuousOnInterval (g ∘ v) a b := by
  unfold AbsolutelyContinuousOnInterval at hv ⊢
  apply squeeze_zero' (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
    ?_ (by simpa only [mul_zero] using hv.const_mul (K : ℝ))
  rw [eventually_inf_principal]
  filter_upwards with I hI
  calc
    _ ≤ ∑ i ∈ Finset.range I.1, (K : ℝ) * dist (v (I.2 i).1) (v (I.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hg.dist_le_mul _ (hvs (hI.1 i hi).1) _ (hvs (hI.1 i hi).2)
    _ = _ := (Finset.mul_sum _ _ _).symm




theorem coordinatewise_ac {N : ℕ} {v : ℝ → EuclideanSpace ℝ (Fin N)} {a b : ℝ}
    (hv : ∀ j, AbsolutelyContinuousOnInterval (fun t => v t j) a b) :
    AbsolutelyContinuousOnInterval v a b := by
  have hnorm (w : EuclideanSpace ℝ (Fin N)) : ‖w‖ ≤ ∑ j, ‖w j‖ := by
    have hw := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr w
    calc
      _ = ‖∑ j, w j • EuclideanSpace.basisFun (Fin N) ℝ j‖ := by
        rw [show (∑ j, w j • EuclideanSpace.basisFun (Fin N) ℝ j) = w from hw]
      _ ≤ ∑ j, ‖w j • EuclideanSpace.basisFun (Fin N) ℝ j‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_smul, OrthonormalBasis.norm_eq_one, mul_one]
  unfold AbsolutelyContinuousOnInterval at hv ⊢
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => hv j)
  simp only [Finset.sum_const_zero] at hsum
  apply squeeze_zero (fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg) ?_ hsum
  intro I
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  simpa only [dist_eq_norm, PiLp.sub_apply] using hnorm (v (I.2 i).1 - v (I.2 i).2)





theorem increment_ae_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {v d : ℝ → E} {a b : ℝ} (hab : a < b)
    (hd : IntervalIntegrable d volume a b)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, v t - v s = ∫ θ in s..t, d θ) :
    ∀ᵐ t ∂volume.restrict (Icc a b), HasDerivAt v (d t) t := by
  have hna : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by simp [ae_iff, measure_singleton]
  have hnb : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_of_ae hd.ae_hasDerivAt_integral,
    ae_restrict_of_ae hna, ae_restrict_of_ae hnb,
    ae_restrict_mem measurableSet_Icc] with t ht hta htb htI
  have htopen : t ∈ Ioo a b :=
    ⟨lt_of_le_of_ne htI.1 hta.symm, lt_of_le_of_ne htI.2 htb⟩
  have hD := (ht (by simpa only [uIcc_of_le hab.le] using htI) a
    (by simp only [uIcc_of_le hab.le, left_mem_Icc, hab.le])).const_add (v a)
  apply hD.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds htopen] with y hy
  exact (eq_add_of_sub_eq (hinc a ⟨le_rfl, hab.le⟩ y ⟨hy.1.le, hy.2.le⟩)).trans
    (add_comm _ _)




theorem ac_chain_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {v d : ℝ → E} {g : E → ℝ}
    {a b : ℝ} {S : Set E} {K : ℝ≥0} (hab : a < b)
    (hv : AbsolutelyContinuousOnInterval v a b) (hg : LipschitzOnWith K g S)
    (hvs : MapsTo v (uIcc a b) S)
    (hgD : ∀ t ∈ Icc a b, DifferentiableAt ℝ g (v t))
    (hd : IntervalIntegrable d volume a b)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, v t - v s = ∫ θ in s..t, d θ) :
    AbsolutelyContinuousOnInterval (g ∘ v) a b ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        HasDerivAt (g ∘ v) (fderiv ℝ g (v t) (d t)) t) ∧
      IntervalIntegrable (fun t => fderiv ℝ g (v t) (d t)) volume a b ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        g (v t) - g (v s) = ∫ θ in s..t, fderiv ℝ g (v θ) (d θ) := by
  have hAC := ac_comp_lipschitz hv hg hvs
  have hchain : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt (g ∘ v) (fderiv ℝ g (v t) (d t)) t := by
    filter_upwards [increment_ae_hasDerivAt hab hd hinc,
      ae_restrict_mem measurableSet_Icc] with t ht htI
    exact (hgD t htI).hasFDerivAt.comp_hasDerivAt t ht
  have heq : deriv (g ∘ v) =ᵐ[volume.restrict (Icc a b)]
      fun t => fderiv ℝ g (v t) (d t) := hchain.mono fun _ ht => ht.deriv
  have hI : IntervalIntegrable (fun t => fderiv ℝ g (v t) (d t)) volume a b :=
    hAC.intervalIntegrable_deriv.congr_ae (ae_restrict_of_ae_restrict_of_subset
      (by simpa only [uIoc_of_le hab.le] using Ioc_subset_Icc_self) heq)
  refine ⟨hAC, hchain, hI, fun s hs t ht => ?_⟩
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact uIcc_subset_Icc hs ht
  change (g ∘ v) t - (g ∘ v) s = _
  rw [← (hAC.mono hsub).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae_restrict
  exact ae_restrict_of_ae_restrict_of_subset
    (uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)) heq

end PoincareConjecture.M65Interior
