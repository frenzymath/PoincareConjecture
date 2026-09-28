import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.TimeDerivatives.Equation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace Poincare.Parabolic.Interior

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_linearMap_le_spatial_add_time (L : E × ℝ →L[ℝ] F) :
    ‖L‖ ≤ ‖L.comp (ContinuousLinearMap.inl ℝ E ℝ)‖ + ‖L (0, 1)‖ := by
  apply L.opNorm_le_bound (by positivity)
  intro p
  have heq : L p = L (p.1, 0) + p.2 • L (0, 1) := by
    rw [← map_smul, ← map_add]
    congr 1
    ext <;> simp
  rw [heq]
  calc
    _ ≤ ‖L (p.1, 0)‖ + ‖p.2 • L (0, 1)‖ := norm_add_le _ _
    _ ≤ ‖L.comp (ContinuousLinearMap.inl ℝ E ℝ)‖ * ‖p.1‖ +
        ‖p.2‖ * ‖L (0, 1)‖ := by
      rw [norm_smul]
      exact add_le_add ((L.comp (ContinuousLinearMap.inl ℝ E ℝ)).le_opNorm p.1) le_rfl
    _ ≤ (‖L.comp (ContinuousLinearMap.inl ℝ E ℝ)‖ + ‖L (0, 1)‖) * ‖p‖ := by
      rw [add_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (norm_fst_le p) (norm_nonneg _)
      · rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (norm_snd_le p) (norm_nonneg _)

theorem norm_iteratedFDeriv_succ_le_spatial_add_time
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (p : E × ℝ) :
    ‖iteratedFDeriv ℝ (m + 1) f p‖ ≤
      ‖iteratedFDeriv ℝ m (spatialDerivative f) p‖ +
        ‖iteratedFDeriv ℝ m (timeDerivative f) p‖ := by
  let S : (E × ℝ →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
    (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip
      (ContinuousLinearMap.inl ℝ E ℝ)
  let T : (E × ℝ →L[ℝ] F) →L[ℝ] F :=
    ContinuousLinearMap.apply ℝ F (0, 1)
  have hs := S.iteratedFDeriv_comp_left (x := p)
    (hf.fderiv_right (m := ∞) (by simp)).contDiffAt (i := m)
      (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  have ht := T.iteratedFDeriv_comp_left (x := p)
    (hf.fderiv_right (m := ∞) (by simp)).contDiffAt (i := m)
      (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  rw [← norm_iteratedFDeriv_fderiv]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hsp : (iteratedFDeriv ℝ m (fderiv ℝ f) p v).comp
      (ContinuousLinearMap.inl ℝ E ℝ) =
        iteratedFDeriv ℝ m (spatialDerivative f) p v := by
    exact (congrArg (fun A => A v) hs).symm
  have htm : iteratedFDeriv ℝ m (fderiv ℝ f) p v (0, 1) =
      iteratedFDeriv ℝ m (timeDerivative f) p v := by
    exact (congrArg (fun A => A v) ht).symm
  calc
    _ ≤ ‖(iteratedFDeriv ℝ m (fderiv ℝ f) p v).comp
          (ContinuousLinearMap.inl ℝ E ℝ)‖ +
        ‖iteratedFDeriv ℝ m (fderiv ℝ f) p v (0, 1)‖ :=
      norm_linearMap_le_spatial_add_time _
    _ = ‖iteratedFDeriv ℝ m (spatialDerivative f) p v‖ +
        ‖iteratedFDeriv ℝ m (timeDerivative f) p v‖ := by rw [hsp, htm]
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add (ContinuousMultilinearMap.le_opNorm _ v)
        (ContinuousMultilinearMap.le_opNorm _ v)

theorem contDiff_iterate_timeDerivative {f : E × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ ((timeDerivative^[j]) f) := by
  induction j with
  | zero => exact hf
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact contDiff_timeDerivative ih

theorem iterate_timeDerivative_spatialDerivative {f : E × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    (timeDerivative^[j]) (spatialDerivative f) =
      spatialDerivative ((timeDerivative^[j]) f) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih,
      timeDerivative_spatialDerivative (contDiff_iterate_timeDerivative hf j),
      Function.iterate_succ_apply']

theorem norm_iteratedFDeriv_le_of_mixed_bounds
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (p : E × ℝ)
    {B : ℝ}
    (hbound : ∀ i j : ℕ, i + j = m →
      ‖iteratedFDeriv ℝ i (fun y => ((timeDerivative^[j]) f) (y, p.2)) p.1‖ ≤ B) :
    ‖iteratedFDeriv ℝ m f p‖ ≤ 2 ^ m * B := by
  induction m generalizing F with
  | zero => simpa using hbound 0 0 rfl
  | succ m ih =>
    have hs : ‖iteratedFDeriv ℝ m (spatialDerivative f) p‖ ≤ 2 ^ m * B := by
      apply ih (contDiff_spatialDerivative hf)
      intro i j hij
      rw [iterate_timeDerivative_spatialDerivative hf]
      have heq : (fun y => spatialDerivative ((timeDerivative^[j]) f) (y, p.2)) =
          fderiv ℝ (fun y => ((timeDerivative^[j]) f) (y, p.2)) := by
        funext y
        exact (fderiv_spatialSlice (contDiff_iterate_timeDerivative hf j) y p.2).symm
      rw [heq, norm_iteratedFDeriv_fderiv]
      exact hbound (i + 1) j (by omega)
    have ht : ‖iteratedFDeriv ℝ m (timeDerivative f) p‖ ≤ 2 ^ m * B := by
      apply ih (contDiff_timeDerivative hf)
      intro i j hij
      rw [← Function.iterate_succ_apply]
      exact hbound i (j + 1) (by omega)
    calc
      _ ≤ ‖iteratedFDeriv ℝ m (spatialDerivative f) p‖ +
          ‖iteratedFDeriv ℝ m (timeDerivative f) p‖ :=
        norm_iteratedFDeriv_succ_le_spatial_add_time hf m p
      _ ≤ 2 ^ m * B + 2 ^ m * B := add_le_add hs ht
      _ = 2 ^ (m + 1) * B := by ring

theorem norm_iteratedFDeriv_le_of_mixed_bounds_on [FiniteDimensional ℝ E]
    {U : Set (E × ℝ)} (hU : IsOpen U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) (p : E × ℝ) (hp : p ∈ U)
    {B : ℝ}
    (hbound : ∀ i j : ℕ, i + j = m →
      ‖iteratedFDeriv ℝ i (fun y => ((timeDerivative^[j]) f) (y, p.2)) p.1‖ ≤ B) :
    ‖iteratedFDeriv ℝ m f p‖ ≤ 2 ^ m * B := by
  obtain ⟨g, hg, _, hgf⟩ := exists_compact_smooth_extension
    (isCompact_singleton (x := p)) hU (singleton_subset_iff.mpr hp) hf
  have he := hgf p (mem_singleton p)
  rw [← (he.iteratedFDeriv ℝ m).eq_of_nhds]
  apply norm_iteratedFDeriv_le_of_mixed_bounds hg m p
  intro i j hij
  have hslice : (fun y => ((timeDerivative^[j]) g) (y, p.2)) =ᶠ[𝓝 p.1]
      (fun y => ((timeDerivative^[j]) f) (y, p.2)) :=
    (iterate_timeDerivative_eventuallyEq he j).comp_tendsto
      (continuousAt_id.prodMk continuousAt_const)
  rw [(hslice.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hbound i j hij

theorem norm_iteratedFDeriv_le_mixed_sum_on [FiniteDimensional ℝ E]
    {U : Set (E × ℝ)} (hU : IsOpen U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) (p : E × ℝ) (hp : p ∈ U)
    (B : ℕ → ℕ → ℝ)
    (hbound : ∀ i j : ℕ, i + j = m →
      ‖iteratedFDeriv ℝ i (fun y => ((timeDerivative^[j]) f) (y, p.2)) p.1‖ ≤ B i j) :
    ‖iteratedFDeriv ℝ m f p‖ ≤
      2 ^ m * ∑ i ∈ Finset.range (m + 1), max 0 (B i (m - i)) := by
  apply norm_iteratedFDeriv_le_of_mixed_bounds_on hU hf m p hp
  intro i j hij
  apply (hbound i j hij).trans
  have hji : m - i = j := by omega
  rw [← hji]
  exact (le_max_right 0 _).trans (Finset.single_le_sum
    (fun k _ => le_max_left 0 (B k (m - k))) (Finset.mem_range.mpr (by omega)))

theorem iterate_timeDerivative_eq_iteratedDeriv {f : E × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : E) (t : ℝ) :
    ((timeDerivative^[j]) f) (x, t) = iteratedDeriv j (fun s => f (x, s)) t := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', iteratedDeriv_succ]
    have h := (hasDerivAt_timeSlice
      ((contDiff_iterate_timeDerivative hf j).differentiable (by simp)) x t).deriv
    simpa only [ih] using h.symm

theorem norm_iteratedFDeriv_le_of_iteratedDeriv_bounds_on [FiniteDimensional ℝ E]
    {U : Set (E × ℝ)} (hU : IsOpen U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) (p : E × ℝ) (hp : p ∈ U)
    {B : ℝ}
    (hbound : ∀ i j : ℕ, i + j = m →
      ‖iteratedFDeriv ℝ i (fun y => iteratedDeriv j (fun s => f (y, s)) p.2) p.1‖ ≤ B) :
    ‖iteratedFDeriv ℝ m f p‖ ≤ 2 ^ m * B := by
  obtain ⟨g, hg, _, hgf⟩ := exists_compact_smooth_extension
    (isCompact_singleton (x := p)) hU (singleton_subset_iff.mpr hp) hf
  have he := hgf p (mem_singleton p)
  rw [← (he.iteratedFDeriv ℝ m).eq_of_nhds]
  apply norm_iteratedFDeriv_le_of_mixed_bounds hg m p
  intro i j hij
  have hslice : (fun y => ((timeDerivative^[j]) g) (y, p.2)) =ᶠ[𝓝 p.1]
      (fun y => iteratedDeriv j (fun s => f (y, s)) p.2) := by
    have hnear := (continuousAt_id.prodMk continuousAt_const :
        Tendsto (fun y : E => (y, p.2)) (𝓝 p.1) (𝓝 p)).eventually
      (eventually_eventuallyEq_nhds.2 he)
    filter_upwards [hnear] with y hy
    rw [iterate_timeDerivative_eq_iteratedDeriv hg]
    have htime : (fun s => g (y, s)) =ᶠ[𝓝 p.2] (fun s => f (y, s)) :=
      hy.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
    exact (htime.iteratedDeriv j).eq_of_nhds
  rw [(hslice.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hbound i j hij

end Poincare.Parabolic.Interior
