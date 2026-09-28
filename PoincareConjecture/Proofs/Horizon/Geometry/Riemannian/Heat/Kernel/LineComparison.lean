import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.NoncompactMaximum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import PoincareConjecture.Proofs.Horizon.Analysis.Heat.GaussianSemigroup









set_option autoImplicit false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
open Poincare.Analysis.Heat

namespace PoincareConjecture.RiemannianMetric




theorem nonpos_of_real_heat_subsolution
    {u ut : ℝ → ℝ → ℝ} {a b B : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (univ ×ˢ Icc a b))
    (hspace : ∀ t ∈ Ioc a b, ContDiff ℝ 2 (fun x => u x t))
    (htime : ∀ x t, t ∈ Ioc a b → HasDerivWithinAt (u x) (ut x t) (Icc a b) t)
    (hheat : ∀ x t, t ∈ Ioc a b → ut x t ≤ deriv (deriv (fun y => u y t)) x)
    (hbound : ∀ x t, t ∈ Icc a b → u x t ≤ B)
    (hinit : ∀ x, u x a ≤ 0) :
    ∀ x t, t ∈ Icc a b → u x t ≤ 0 := by
  have hbarrier (ε : ℝ) (hε : 0 < ε) :
      ∀ x t, t ∈ Icc a b → u x t - ε * (x ^ 2 + 2 * (t - a) + 1) ≤ 0 := by
    let F : ℝ → ℝ → ℝ := fun x t => u x t - ε * (x ^ 2 + 2 * (t - a) + 1)
    let R : ℝ := |B| / ε + 1
    have hR : 1 ≤ R := le_add_of_nonneg_left (div_nonneg (abs_nonneg _) hε.le)
    apply Poincare.Parabolic.nonpos_of_deriv_le_mul_at_max_of_nonpos_outside_compact
      (F := F) (F' := fun x t => ut x t - 2 * ε) (c := 0)
      (K := Icc (-R) R) isCompact_Icc
    · exact hcont.sub (by fun_prop)
    · intro x t ht
      have hd : HasDerivAt (fun s : ℝ => ε * (x ^ 2 + 2 * (s - a) + 1))
          (2 * ε) t := by
        convert! ((((hasDerivAt_id t).sub_const a).const_mul 2).const_add (x ^ 2)
          |>.add_const 1 |>.const_mul ε) using 1
        ring
      exact (htime x t ht).sub hd.hasDerivWithinAt
    · intro x t ht _ hmax
      have hdiff := (hspace t ht).differentiable (by norm_num)
      have hderiv : deriv (fun y => F y t) =
          fun y => deriv (fun z => u z t) y - ε * (2 * y) := by
        funext y
        have hd : HasDerivAt (fun z : ℝ => ε * (z ^ 2 + 2 * (t - a) + 1))
            (ε * (2 * y)) y := by
          convert! ((((hasDerivAt_id y).pow 2).add_const (2 * (t - a))).add_const 1
            |>.const_mul ε) using 1
          simp only [id_eq]
          ring
        exact ((hdiff y).hasDerivAt.sub hd).deriv
      have hsecond : deriv (deriv (fun y => F y t)) x =
          deriv (deriv (fun y => u y t)) x - 2 * ε := by
        rw [hderiv]
        have hdd := (hspace t ht).differentiable_deriv_two
        convert! ((hdd x).hasDerivAt.sub
          (((hasDerivAt_id x).const_mul 2).const_mul ε)).deriv using 1
        ring
      have hnonpos := LeviCivitaData.deriv_deriv_nonpos_of_isLocalMax
        (φ := fun y => F y t) (Eventually.of_forall hmax)
        ((hdiff x).continuousAt.sub (by fun_prop))
      rw [hsecond] at hnonpos
      simpa only [zero_mul] using (sub_le_sub_right (hheat x t ht) (2 * ε)).trans hnonpos
    · intro x
      dsimp only [F]
      have hp : 0 ≤ ε * (x ^ 2 + 2 * (a - a) + 1) := by simp only [sub_self]; positivity
      linarith [hinit x]
    · intro x hx t ht
      have habs : R < |x| := by
        by_contra hh
        have hh' := abs_le.mp (le_of_not_gt hh)
        exact hx hh'
      have hsq : |x| ≤ x ^ 2 := by
        nlinarith [sq_abs x]
      have hB : B < ε * x ^ 2 := by
        have hd : |B| = ε * (|B| / ε) := by field_simp
        have hlarge : |B| / ε < x ^ 2 := by dsimp only [R] at habs; linarith
        have hm := mul_lt_mul_of_pos_left hlarge hε
        rw [← hd] at hm
        exact (le_abs_self B).trans_lt hm
      dsimp only [F]
      have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
      have hp : 0 ≤ ε * (2 * (t - a) + 1) := by positivity
      nlinarith [hbound x t ht]
  intro x t ht
  have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
  have hden : 0 < x ^ 2 + 2 * (t - a) + 1 := by positivity
  apply le_of_forall_pos_le_add
  intro δ hδ
  have h := hbarrier (δ / (x ^ 2 + 2 * (t - a) + 1)) (by positivity) x t ht
  rw [div_mul_cancel₀ _ hden.ne'] at h
  linarith

private theorem continuous_gaussianAverage_of_bounded
    {f : ℝ → ℝ} (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    Continuous (fun p : ℝ × ℝ => gaussianAverage f p.2 p.1) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => B)
  · intro p
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro p
    exact Eventually.of_forall fun z => hB _
  · exact integrable_const B
  · exact Eventually.of_forall fun z => hf.comp (by fun_prop)



theorem gaussianAverage_le_nonnegative_supersolution
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hdf : Differentiable ℝ f) {B : ℝ} (hfB : ∀ x, ‖f x‖ ≤ B)
    {u ut : ℝ → ℝ → ℝ} {T : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (univ ×ˢ Icc 0 T))
    (hspace : ∀ t ∈ Ioc 0 T, ContDiff ℝ 2 (fun x => u x t))
    (htime : ∀ x t, t ∈ Ioc 0 T → HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t)
    (hheat : ∀ x t, t ∈ Ioc 0 T → deriv (deriv (fun y => u y t)) x ≤ ut x t)
    (hnonneg : ∀ x t, t ∈ Icc 0 T → 0 ≤ u x t)
    (hinit : ∀ x, f x ≤ u x 0) :
    ∀ x t, t ∈ Icc 0 T → gaussianAverage f t x ≤ u x t := by
  have hdiff : ∀ t ∈ Ioc 0 T, ContDiff ℝ 2 (gaussianAverage f t) :=
    fun t ht => (contDiff_infty.mp (contDiff_gaussianAverage hf hdf ht.1)) 2
  have hsecond (t : ℝ) (ht : t ∈ Ioc 0 T) (x : ℝ) :
      deriv (deriv (fun y => gaussianAverage f t y - u y t)) x =
        deriv (deriv (gaussianAverage f t)) x - deriv (deriv (fun y => u y t)) x := by
    have heq : deriv (fun y => gaussianAverage f t y - u y t) =
        fun y => deriv (gaussianAverage f t) y - deriv (fun z => u z t) y := by
      funext y
      exact (((hdiff t ht).differentiable (by norm_num) y).hasDerivAt.sub
        ((hspace t ht).differentiable (by norm_num) y).hasDerivAt).deriv
    rw [heq]
    exact (((hdiff t ht).differentiable_deriv_two x).hasDerivAt.sub
      ((hspace t ht).differentiable_deriv_two x).hasDerivAt).deriv
  have h := nonpos_of_real_heat_subsolution
    (u := fun x t => gaussianAverage f t x - u x t)
    (ut := fun x t => deriv (deriv (gaussianAverage f t)) x - ut x t)
    ((continuous_gaussianAverage_of_bounded hf.continuous hfB).continuousOn.sub hcont)
    (fun t ht => (hdiff t ht).sub (hspace t ht))
    (fun x t ht => (gaussianAverage_heatEquation hf hdf ht.1 x).hasDerivWithinAt.sub
      (htime x t ht))
    (fun x t ht => by rw [hsecond t ht x]; linarith [hheat x t ht])
    (B := B) (fun x t ht => ?_) (fun x => ?_)
  · exact fun x t ht => sub_nonpos.mp (h x t ht)
  · have hb : gaussianAverage f t x ≤ B := by
      have hh := norm_integral_le_of_norm_le_const
        (μ := gaussianReal 0 1) (Eventually.of_forall fun z => hfB (x + Real.sqrt (2 * t) * z))
      have hi : ‖gaussianAverage f t x‖ ≤ B := by
        simpa only [gaussianAverage, probReal_univ, mul_one] using hh
      exact (le_abs_self _).trans hi
    linarith [hnonneg x t ht]
  · simpa [gaussianAverage] using sub_nonpos.mpr (hinit x)

end PoincareConjecture.RiemannianMetric
