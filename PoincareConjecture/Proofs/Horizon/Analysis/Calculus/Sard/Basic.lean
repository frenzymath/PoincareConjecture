import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.MeasureTheory.Function.Jacobian

open MeasureTheory Set
open scoped ContDiff

namespace Poincare.Analysis

noncomputable def lineMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y v : E) : ℝ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight v

theorem iteratedFDeriv_lineMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (y v : E) (i : ℕ)
    (hf : ContDiff ℝ i f) (t : ℝ) :
    iteratedFDeriv ℝ i (fun u : ℝ => f (y + u • v)) t =
      (iteratedFDeriv ℝ i f (y + t • v)).compContinuousLinearMap
        (fun _ : Fin i => lineMap y v) := by
  let g : E → F := fun z => f (y + z)
  have hg : ContDiff ℝ i g := by
    change ContDiff ℝ i (f ∘ fun z : E => y + z)
    exact hf.comp (contDiff_const.add contDiff_id)
  have hcomp := ContinuousLinearMap.iteratedFDeriv_comp_right
    (lineMap y v) (f := g) hg t (i := i) (by rfl)
  simp only [g, lineMap] at hcomp
  rw [iteratedFDeriv_comp_add_left] at hcomp
  have hline : (fun u : ℝ => f (y + u • v)) =
      (fun z : E => f (y + z)) ∘ lineMap y v := by
    funext u
    rfl
  rw [hline]
  exact hcomp

theorem norm_sub_le_of_flat_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x y : E} {n : ℕ} {C : ℝ}
    (hf : ∀ (t : ℝ) (_ht : t ∈ Icc 0 1),
      ContDiffAt ℝ (n + 1) f (x + t • y))
    (hflat : ∀ k, 1 ≤ k → k ≤ n →
      iteratedFDeriv ℝ k f x (fun _ : Fin k => y) = 0)
    (hbound : ∀ (t : ℝ) (_ht : t ∈ Icc 0 1),
      ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)
        (fun _ : Fin (n + 1) => y)‖ ≤ C) :
    ‖f (x + y) - f x‖ ≤ C / (Nat.factorial n : ℝ) := by
  have sum_flat : ∀ N : ℕ, (∀ k, 1 ≤ k → k ≤ N →
      iteratedFDeriv ℝ k f x (fun _ : Fin k => y) = 0) →
      (∑ k ∈ Finset.range (N + 1),
        (Nat.factorial k : ℝ)⁻¹ •
          (iteratedFDeriv ℝ k f x (fun _ : Fin k => y))) = f x := by
    intro N hN
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih (fun k hk hkn => hN k hk (by omega))]
      have hz := hN (n + 1) (by omega) (by omega)
      simp [hz]
  have hsum := sum_flat n hflat
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := x) (y := y) (n := n) hf
  rw [hTaylor, hsum]
  rw [add_sub_cancel_left]
  rw [norm_smul]
  have hInt : ‖∫ t in (0 : ℝ)..1,
      (1 - t) ^ n • (iteratedFDeriv ℝ (n + 1) f (x + t • y))
        (fun _ : Fin (n + 1) => y)‖ ≤ C := by
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C)
      (f := fun t : ℝ => (1 - t) ^ n •
        (iteratedFDeriv ℝ (n + 1) f (x + t • y))
          (fun _ : Fin (n + 1) => y))
      (by
        intro t ht
        rw [uIoc_of_le (by norm_num)] at ht
        rw [norm_smul]
        rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
        have hp : (1 - t) ^ n ≤ (1 : ℝ) := by
          exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
        calc
          (1 - t) ^ n * ‖(iteratedFDeriv ℝ (n + 1) f (x + t • y))
              (fun _ : Fin (n + 1) => y)‖ ≤
              1 * ‖(iteratedFDeriv ℝ (n + 1) f (x + t • y))
                (fun _ : Fin (n + 1) => y)‖ :=
            mul_le_mul_of_nonneg_right hp (norm_nonneg _)
          _ ≤ C := by simpa using hbound t ⟨ht.1.le, ht.2⟩)
    simpa using hI
  have hn : 0 ≤ (Nat.factorial n : ℝ)⁻¹ := by positivity
  calc
    ‖(Nat.factorial n : ℝ)⁻¹‖ * ‖∫ t in (0 : ℝ)..1,
        (1 - t) ^ n • (iteratedFDeriv ℝ (n + 1) f (x + t • y))
          (fun _ : Fin (n + 1) => y)‖ =
        (Nat.factorial n : ℝ)⁻¹ * ‖∫ t in (0 : ℝ)..1,
        (1 - t) ^ n • (iteratedFDeriv ℝ (n + 1) f (x + t • y))
          (fun _ : Fin (n + 1) => y)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
    _ ≤ (Nat.factorial n : ℝ)⁻¹ * C :=
      mul_le_mul_of_nonneg_left hInt hn
    _ = C / (Nat.factorial n : ℝ) := by
      rw [div_eq_mul_inv, mul_comm]

theorem iteratedFDeriv_apply_const_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    {D : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) F}
    {v : E} {C : ℝ} (hD : ‖D‖ ≤ C) :
    ‖D (fun _ : Fin (n + 1) => v)‖ ≤ C * ‖v‖ ^ (n + 1) := by
  calc
    ‖D (fun _ : Fin (n + 1) => v)‖ ≤ ‖D‖ * ∏ _ : Fin (n + 1), ‖v‖ := D.le_opNorm _
    _ ≤ C * ‖v‖ ^ (n + 1) := by
      rw [Finset.prod_const, Finset.card_fin]
      gcongr

theorem norm_sub_le_of_flat_iteratedFDeriv_of_norm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x y : E} {n : ℕ} {C : ℝ}
    (hf : ∀ (t : ℝ) (_ht : t ∈ Icc 0 1),
      ContDiffAt ℝ (n + 1) f (x + t • y))
    (hflat : ∀ k, 1 ≤ k → k ≤ n →
      iteratedFDeriv ℝ k f x (fun _ : Fin k => y) = 0)
    (hbound : ∀ (t : ℝ) (_ht : t ∈ Icc 0 1),
      ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ ≤ C) :
    ‖f (x + y) - f x‖ ≤ C * ‖y‖ ^ (n + 1) / (Nat.factorial n : ℝ) := by
  apply norm_sub_le_of_flat_iteratedFDeriv hf hflat
  intro t ht
  exact iteratedFDeriv_apply_const_le (hbound t ht)

theorem holderOnWith_of_flat_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {s t : Set E} {f : E → F} {n : ℕ} {C : ℝ}
    (hs : Convex ℝ s) (hC : 0 ≤ C)
    (hts : t ⊆ s)
    (hf : ∀ z ∈ s, ContDiffAt ℝ (n + 1) f z)
    (hflat : ∀ z ∈ t, ∀ k, 1 ≤ k → k ≤ n →
      iteratedFDeriv ℝ k f z = 0)
    (hbound : ∀ z ∈ s, ‖iteratedFDeriv ℝ (n + 1) f z‖ ≤ C) :
    HolderOnWith (⟨C / (Nat.factorial n : ℝ), by positivity⟩ : NNReal)
      (⟨(n + 1 : ℕ), by positivity⟩ : NNReal) f t := by
  let K : NNReal := ⟨C / (Nat.factorial n : ℝ), by positivity⟩
  let q : NNReal := ⟨(n + 1 : ℕ), by positivity⟩
  change HolderOnWith K q f t
  intro x hx y hy
  rw [edist_dist, edist_dist]
  rw [dist_eq_norm]
  rw [ENNReal.coe_nnreal_eq]
  change ENNReal.ofReal ‖f x - f y‖ ≤
    ENNReal.ofReal (K : ℝ) * ENNReal.ofReal (dist x y) ^ (q : ℝ)
  have hK : (K : ℝ) = C / (Nat.factorial n : ℝ) := by rfl
  have hq : (q : ℝ) = (n + 1 : ℕ) := by rfl
  rw [hK, hq]
  rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) (by positivity)]
  rw [← ENNReal.ofReal_mul (div_nonneg hC (by positivity))]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_sub_rev]
  rw [dist_eq_norm]
  have hr := norm_sub_le_of_flat_iteratedFDeriv_of_norm_le
    (f := f) (x := x) (y := y - x) (n := n) (C := C)
    (by
      intro t ht
      exact hf _ (hs.add_smul_sub_mem (hts hx) (hts hy) ht))
    (by
      intro k hk hkn
      simpa using congr_arg (fun D => D (fun _ : Fin k => y - x))
        (hflat x hx k hk hkn))
    (by
      intro t ht
      exact hbound _ (hs.add_smul_sub_mem (hts hx) (hts hy) ht))
  have hxy : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
  rw [hxy] at hr
  rw [Real.rpow_natCast]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hr

variable {m n : ℕ}
variable [MeasurableSpace (EuclideanSpace ℝ (Fin m))]
  [BorelSpace (EuclideanSpace ℝ (Fin m))]
  [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
  [BorelSpace (EuclideanSpace ℝ (Fin n))]

theorem measure_zero_image_of_locallyHolderOnWith_of_finrank_div_lt
    {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    {r : NNReal} (hr : 0 < r)
    (hholder :
      ∀ x ∈ s, ∃ C : NNReal, ∃ t ∈ nhdsWithin x s,
        HolderOnWith C r f t)
    (hdim :
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ENNReal) / r <
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :
    μ (f '' s) = 0 := by
  have hsourceDim :
      dimH s ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by
    rw [← Real.dimH_univ_eq_finrank (EuclideanSpace ℝ (Fin m))]
    exact dimH_mono (Set.subset_univ _)
  have hdimImage :
      dimH (f '' s) < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    calc
      dimH (f '' s) ≤ dimH s / r :=
        dimH_image_le_of_locally_holder_on hr hholder
      _ ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ENNReal) / r := by
        exact ENNReal.div_le_div_right hsourceDim r
      _ < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := hdim
  have hhausdorff :
      Measure.hausdorffMeasure
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ)
          (f '' s) = 0 := by
    simpa using hausdorffMeasure_of_dimH_lt hdimImage
  rw [Measure.isAddLeftInvariant_eq_smul μ
    (Measure.hausdorffMeasure (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ))]
  rw [Measure.smul_apply, hhausdorff]
  simp

theorem dense_compl_of_measure_zero_image
    {α : Type*} [AddGroup α] [TopologicalSpace α] [MeasurableSpace α]
    {A : Set α} (μ : Measure α) [μ.IsAddHaarMeasure]
    (hA : μ A = 0) : Dense Aᶜ := by
  rw [dense_iff_inter_open]
  intro U hU hne
  by_contra h
  have hsub : U ⊆ A := by
    intro x hx
    by_contra hxA
    exact h ⟨x, hx, hxA⟩
  have hUzero : μ U = 0 := measure_mono_null hsub hA
  exact (hU.measure_pos μ hne).ne' (by simpa [hUzero])

theorem critical_values_null_one_dim
    {s : Set ℝ} {f : ℝ → ℝ} (μ : Measure ℝ) [μ.IsAddHaarMeasure]
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x)
    (hcrit : ∀ x ∈ s, (fderiv ℝ f x).det = 0) :
    μ (f '' s) = 0 := by
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hf' hcrit

theorem exists_regular_value_one_dim
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {I : Set ℝ}
    (hI : IsOpen I) (hIn : I.Nonempty) :
    ∃ c ∈ I, ∀ x, f x = c → Function.Surjective (fderiv ℝ f x) := by
  let s : Set ℝ := {x | (fderiv ℝ f x).det = 0}
  have hnull : volume (f '' s) = 0 := by
    apply critical_values_null_one_dim volume
    · intro x hx
      exact ((hf.differentiable (by simp)).differentiableAt).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      exact hx
  have hdense : Dense (f '' s)ᶜ :=
    dense_compl_of_measure_zero_image volume hnull
  rcases (dense_iff_inter_open.mp hdense I hI hIn) with ⟨c, hcI, hcn⟩
  refine ⟨c, hcI, ?_⟩
  intro x hxc
  by_contra hsurj
  apply hcn
  refine ⟨x, ?_, hxc⟩
  change (fderiv ℝ f x).det = 0
  have hz : (fderiv ℝ f x).toLinearMap = 0 := by
    have hne : ¬ (fderiv ℝ f x).toLinearMap ≠ 0 := by
      intro hne
      exact hsurj (LinearMap.surjective hne)
    exact not_not.mp hne
  simp [ContinuousLinearMap.det, hz]

theorem dense_regular_values_of_null_critical_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (μ : Measure ℝ) [μ.IsAddHaarMeasure]
    (hcrit : μ (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0) :
    Dense {c : ℝ | ∀ x, f x = c → Function.Surjective (fderiv ℝ f x)} := by
  let C : Set ℝ := f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}
  have hC : Dense Cᶜ := dense_compl_of_measure_zero_image μ hcrit
  have hregular : {c : ℝ | ∀ x, f x = c → Function.Surjective (fderiv ℝ f x)} = Cᶜ := by
    ext c
    constructor
    · intro hc ⟨x, hx, hfx⟩
      exact hx (hc x hfx)
    · intro hc x hfx
      by_contra hns
      exact hc ⟨x, hns, hfx⟩
  rw [hregular]
  exact hC

end Poincare.Analysis
