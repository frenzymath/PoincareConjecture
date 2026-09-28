import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityACComposition
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityOscillation











set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace PoincareConjecture.M65Interior




theorem linear_circle_data {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : E →L[ℝ] G) (c : E) {v d : ℝ → E} {a b : ℝ}
    (hv : AbsolutelyContinuousOnInterval v a b)
    (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, v t - v s = ∫ θ in s..t, d θ) :
    AbsolutelyContinuousOnInterval (fun θ => L (v θ - c)) a b ∧
      MemLp (fun θ => L (d θ)) 2 (volume.restrict (Icc a b)) ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        L (v t - c) - L (v s - c) = ∫ θ in s..t, L (d θ) := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := by
    simp only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero]
    exact tendsto_const_nhds
  refine ⟨ac_comp_lipschitz (hv.sub hconst) L.lipschitz.lipschitzOnWith
    (fun _ _ => mem_univ _), L.comp_memLp' hd, ?_⟩
  intro s hs t ht
  have hdI : IntegrableOn d (Icc a b) := hd.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hi : IntervalIntegrable d volume s t :=
    (hdI.mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
  calc
    _ = L (v t - v s) := by
      rw [← map_sub]
      congr 1
      abel
    _ = L (∫ θ in s..t, d θ) := congrArg L (hinc s hs t ht)
    _ = _ := (L.intervalIntegral_comp_comm hi).symm




theorem interval_increment_energy_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v d : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hv : ContinuousOn v (Icc a b)) (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, v t - v s = ∫ θ in s..t, d θ) :
    (∫ θ in Icc a b, (‖v θ - v a‖ ^ 2 + ‖d θ‖ ^ 2)) ≤
      (1 + (b - a) ^ 2) * ∫ θ in Icc a b, ‖d θ‖ ^ 2 := by
  have hvI : IntegrableOn (fun θ => ‖v θ - v a‖ ^ 2) (Icc a b) :=
    ((hv.sub continuousOn_const).norm.pow 2).integrableOn_compact isCompact_Icc
  have hdI : IntegrableOn (fun θ => ‖d θ‖ ^ 2) (Icc a b) := hd.norm.integrable_sq
  have hpoint := interval_increment_norm_sq_le hab hd hinc a ⟨le_rfl, hab⟩
  have hint : (∫ θ in Icc a b, ‖v θ - v a‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ θ in Icc a b, ‖d θ‖ ^ 2 := by
    have h := integral_mono_ae hvI
      (integrable_const ((b - a) * ∫ θ in Icc a b, ‖d θ‖ ^ 2))
      (ae_restrict_of_forall_mem measurableSet_Icc hpoint)
    simpa only [integral_const, Measure.restrict_apply_univ, Measure.real,
      Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul,
      ← mul_assoc, ← sq] using h
  rw [integral_add hvI hdI]
  nlinarith only [hint]




theorem clm_circle_energy_le {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) {d : ℝ → E} {a b : ℝ}
    (hd : MemLp d 2 (volume.restrict (Icc a b))) :
    (∫ θ in Icc a b, ‖L (d θ)‖ ^ 2) ≤
      ‖L‖ ^ 2 * ∫ θ in Icc a b, ‖d θ‖ ^ 2 := by
  rw [← integral_const_mul]
  apply integral_mono_ae (L.comp_memLp' hd).norm.integrable_sq
    (hd.norm.integrable_sq.const_mul (‖L‖ ^ 2))
  apply ae_of_all
  intro θ
  simpa +instances only [Function.comp_apply, mul_pow] using!
    pow_le_pow_left₀ (norm_nonneg (L (d θ))) (L.le_opNorm (d θ)) 2

end PoincareConjecture.M65Interior
