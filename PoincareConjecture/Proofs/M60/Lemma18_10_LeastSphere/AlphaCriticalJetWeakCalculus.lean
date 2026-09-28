import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSourceWeakChain
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.TestCalculus









set_option autoImplicit false

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal
open Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60



theorem suWeakPartial_mul
    {f g : LoopPlane → ℝ} {Df Dg : Fin 2 → LoopPlane → ℝ}
    {a : LoopPlane} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : MemLp f 4 (volume.restrict (ball a R)))
    (hg : MemLp g 4 (volume.restrict (ball a R)))
    (hDf : ∀ i, MemLp (Df i) 2 (volume.restrict (ball a R)))
    (hDg : ∀ i, MemLp (Dg i) 2 (volume.restrict (ball a R)))
    (hwf : ∀ i, HasWeakPartialDeriv i (Df i) f (ball a R))
    (hwg : ∀ i, HasWeakPartialDeriv i (Dg i) g (ball a R)) (i : Fin 2) :
    HasWeakPartialDeriv i (fun x => Df i x * g x + f x * Dg i x)
      (fun x => f x * g x) (ball a r) := by
  let U : LoopPlane → EuclideanSpace ℝ (Fin 2) := fun x => WithLp.toLp 2 ![f x, g x]
  let W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin 2) :=
    fun j x => WithLp.toLp 2 ![Df j x, Dg j x]
  let F : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => y 0 * y 1
  have hU : MemLp U 4 (volume.restrict (ball a R)) := by
    apply MemLp.of_eval_piLp
    intro b
    fin_cases b
    · exact hf
    · exact hg
  have hW (j : Fin 2) : MemLp (W j) 2 (volume.restrict (ball a R)) := by
    apply MemLp.of_eval_piLp
    intro b
    fin_cases b
    · exact hDf j
    · exact hDg j
  have hw (j b : Fin 2) : HasWeakPartialDeriv j (fun x => W j x b)
      (fun x => U x b) (ball a R) := by
    fin_cases b
    · exact hwf j
    · exact hwg j
  have hF : ContDiff ℝ 1 F :=
    (show ContDiff ℝ 1 (fun y : LoopPlane => y 0) from
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).mul
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff
  have hd (y : EuclideanSpace ℝ (Fin 2)) : fderiv ℝ F y =
      y 0 • EuclideanSpace.proj 1 + y 1 • EuclideanSpace.proj 0 := by
    exact (((EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) 1).hasFDerivAt)).fderiv
  have hb (y : EuclideanSpace ℝ (Fin 2)) : ‖fderiv ℝ F y‖ ≤ 2 * (1 + ‖y‖ ^ 2) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [hd]
    change ‖y 0 * v 1 + y 1 * v 0‖ ≤ _
    calc
      _ ≤ ‖y 0‖ * ‖v 1‖ + ‖y 1‖ * ‖v 0‖ := by
        simpa only [norm_mul] using norm_add_le (y 0 * v 1) (y 1 * v 0)
      _ ≤ ‖y‖ * ‖v‖ + ‖y‖ * ‖v‖ := add_le_add
        (mul_le_mul (PiLp.norm_apply_le y 0) (PiLp.norm_apply_le v 1)
          (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (PiLp.norm_apply_le y 1) (PiLp.norm_apply_le v 0)
          (norm_nonneg _) (norm_nonneg _))
      _ = (2 * ‖y‖) * ‖v‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (‖y‖ - 1)])
        (norm_nonneg v)
  have ht := suWeakPartial_comp_quadratic hr hrR hU hW hw hF
    (show (0 : ℝ) < 2 by norm_num) hb i
  simpa only [hd, add_apply, smul_apply,
    PiLp.proj_apply, smul_eq_mul, U, W, F, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_comm, add_comm] using ht



theorem suWeakDivergence_eq_ae
    {O : Set LoopPlane} (hO : IsOpen O)
    {F DF : Fin 2 → LoopPlane → ℝ} {b : LoopPlane → ℝ}
    (hF : ∀ i, IntegrableOn (F i) O) (hDF : ∀ i, IntegrableOn (DF i) O)
    (hb : IntegrableOn b O)
    (hw : ∀ i, HasWeakPartialDeriv i (DF i) (F i) O)
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O →
      (∫ x in O, ∑ i : Fin 2, F i x * fderiv ℝ phi x (EuclideanSpace.single i 1)) =
        ∫ x in O, b x * phi x) :
    ∀ᵐ x ∂volume.restrict O, (∑ i : Fin 2, DF i x) + b x = 0 := by
  have hI : IntegrableOn (fun x => (∑ i : Fin 2, DF i x) + b x) O :=
    (integrable_finsetSum _ (fun i _ => hDF i)).add hb
  rw [ae_restrict_iff' hO.measurableSet]
  apply hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrableOn_of_locallyIntegrable_restrict hI.locallyIntegrable)
  intro phi hp hc hs
  have hiD (i : Fin 2) := Poincare.Analysis.Elliptic.Iteration.integrable_mul_test
    (hDF i).locallyIntegrable hp hc
  have hiF (i : Fin 2) : Integrable
      (fun x => F i x * fderiv ℝ phi x (EuclideanSpace.single i 1)) (volume.restrict O) :=
    Poincare.Analysis.Elliptic.Iteration.integrable_mul_partial_test
      (hF i).locallyIntegrable hp hc i
  have hib := Poincare.Analysis.Elliptic.Iteration.integrable_mul_test hb.locallyIntegrable hp hc
  have he := heq phi hp hc hs
  rw [integral_finsetSum _ (fun i _ => hiF i)] at he
  simp_rw [hw _ phi hp hc hs, Finset.sum_neg_distrib] at he
  have hz : ∀ x, x ∉ O → phi x • ((∑ i : Fin 2, DF i x) + b x) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), zero_smul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  simp only [smul_eq_mul, mul_add, Finset.mul_sum]
  simp_rw [mul_comm (phi _)]
  rw [integral_add (integrable_finsetSum _ (fun i _ => hiD i)) hib,
    integral_finsetSum _ (fun i _ => hiD i)]
  linarith

end PoincareConjecture.M60
