import PoincareConjecture.Proofs.M63.Mathlib.ClassicalPrimitive
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology





theorem iteratedDeriv_primitive_and_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b) {q R : ℝ → ℝ → E}
    (hq : ∀ t ∈ Icc a b, ContDiff ℝ ∞ (q t))
    (hR : ∀ t ∈ Icc a b, ContDiff ℝ ∞ (R t))
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (R z.1) z.2) (Icc a b ×ˢ univ))
    (hprimitive : ∀ t ∈ Icc a b, ∀ x,
      q t x = q a x + ∫ r in a..t, R r x) :
    ∀ k : ℕ,
      (∀ t ∈ Icc a b, ∀ x, iteratedDeriv k (q t) x =
        iteratedDeriv k (q a) x + ∫ r in a..t, iteratedDeriv k (R r) x) ∧
      ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun r => iteratedDeriv k (q r) x)
        (iteratedDeriv k (R t) x) t := by
  have hqd (k : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      HasDerivAt (iteratedDeriv k (q t)) (iteratedDeriv (k + 1) (q t) x) x := by
    simpa only [iteratedDeriv_succ] using
      ((hq t ht).differentiable_iteratedDeriv k
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) x).hasDerivAt
  have hRd (k : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      HasDerivAt (iteratedDeriv k (R t)) (iteratedDeriv (k + 1) (R t) x) x := by
    simpa only [iteratedDeriv_succ] using
      ((hR t ht).differentiable_iteratedDeriv k
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) x).hasDerivAt
  have hcont (k : ℕ) (x : ℝ) :
      ContinuousOn (fun r => iteratedDeriv k (R r) x) (Icc a b) :=
    (hjets k).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hr, mem_univ _⟩)
  have hint (k : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      IntervalIntegrable (fun r => iteratedDeriv k (R r) x) volume a t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1
      ((hcont k x).mono (Icc_subset_Icc_right ht.2))
  have hprim : ∀ k : ℕ, ∀ t ∈ Icc a b, ∀ x, iteratedDeriv k (q t) x =
      iteratedDeriv k (q a) x + ∫ r in a..t, iteratedDeriv k (R r) x := by
    intro k
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hprimitive
    | succ k ih =>
      intro t ht x
      obtain ⟨C, hC⟩ := (isCompact_Icc.prod
        (isCompact_Icc : IsCompact (Icc (x - 1) (x + 1)))).exists_bound_of_continuousOn
          ((hjets (k + 1)).mono (prod_mono_right (subset_univ _)))
      have hdint := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := fun y r => iteratedDeriv k (R r) y)
        (F' := fun y r => iteratedDeriv (k + 1) (R r) y)
        (x₀ := x) (s := Ioo (x - 1) (x + 1)) (bound := fun _ => C)
        (a := a) (b := t) (Ioo_mem_nhds (by linarith) (by linarith))
        (Eventually.of_forall fun y => (hint k t ht y).def'.aestronglyMeasurable)
        (hint k t ht x) (hint (k + 1) t ht x).def'.aestronglyMeasurable
        (Eventually.of_forall fun r hr y hy => by
          rw [uIoc_of_le ht.1] at hr
          exact hC (r, y) ⟨⟨hr.1.le, hr.2.trans ht.2⟩, hy.1.le, hy.2.le⟩)
        intervalIntegrable_const
        (Eventually.of_forall fun r hr y _ => by
          rw [uIoc_of_le ht.1] at hr
          exact hRd k r ⟨hr.1.le, hr.2.trans ht.2⟩ y)
      have heq : iteratedDeriv k (q t) = fun y =>
          iteratedDeriv k (q a) y + ∫ r in a..t, iteratedDeriv k (R r) y :=
        funext (ih t ht)
      have hsum : HasDerivAt (iteratedDeriv k (q t))
          (iteratedDeriv (k + 1) (q a) x +
            ∫ r in a..t, iteratedDeriv (k + 1) (R r) x) x := by
        rw [heq]
        exact (hqd k a ⟨le_rfl, hab⟩ x).add hdint.2
      exact (hqd k t ht x).unique hsum
  intro k
  refine ⟨hprim k, ?_⟩
  intro t ht x
  exact hasDerivAt_of_ae_continuous_primitive hab
    (hint k b ⟨hab, le_rfl⟩ x) (hcont k x) Filter.EventuallyEq.rfl
    (fun s hs => hprim k s hs x) ht
