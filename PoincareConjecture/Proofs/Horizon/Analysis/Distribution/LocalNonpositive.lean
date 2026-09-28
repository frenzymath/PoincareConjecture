import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrableOn_integral_nonpos_of_locally_test_nonpos
    (μ : Measure E) {D : Set E} (A : (E → ℝ) → E → ℝ)
    (hadd : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      A (fun x => f x + g x) = fun x => A f x + A g x)
    (hzero : ∀ f : E → ℝ, ContDiff ℝ ∞ f → ∀ x ∉ tsupport f, A f x = 0)
    (hlocal : ∀ x ∈ D, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ D ∧
      ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ U → (∀ y, 0 ≤ ψ y) →
        IntegrableOn (A ψ) U μ ∧ (∫ y in U, A ψ y ∂μ) ≤ 0)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ D) (hφ0 : ∀ x, 0 ≤ φ x) :
    IntegrableOn (A φ) D μ ∧ (∫ x in D, A φ x ∂μ) ≤ 0 := by
  classical
  choose U hUopen hUmem hUD hUtest using fun x : D => hlocal x x.property
  have hcover : tsupport φ ⊆ ⋃ x : D, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hφD hx⟩, hUmem _⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, E) (isClosed_tsupport φ) U hUopen hcover
  have hfinite := ρ.locallyFinite.finite_nonempty_inter_compact hφc.isCompact
  let s : Finset D := hfinite.toFinset
  let ψ : D → E → ℝ := fun i x => ρ i x * φ x
  have hψ (i : D) : ContDiff ℝ ∞ (ψ i) := (ρ i).contMDiff.contDiff.mul hφ
  have hψc (i : D) : HasCompactSupport (ψ i) := hφc.mul_left
  have hψU (i : D) : tsupport (ψ i) ⊆ U i := tsupport_mul_subset_left.trans (hρ i)
  have hψ0 (i : D) (x : E) : 0 ≤ ψ i x := mul_nonneg (ρ.nonneg i x) (hφ0 x)
  have hsum : (fun x => ∑ i ∈ s, ψ i x) = φ := by
    funext x
    have hs : Function.support (fun i => ψ i x) ⊆ s := by
      intro i hi
      apply hfinite.mem_toFinset.mpr
      exact ⟨x, (mul_ne_zero_iff.mp hi).1, subset_tsupport φ (mul_ne_zero_iff.mp hi).2⟩
    rw [← finsum_eq_sum_of_support_subset _ hs]
    change (∑ᶠ i, ρ i x * φ x) = φ x
    rw [← finsum_mul]
    by_cases hx : x ∈ tsupport φ
    · rw [ρ.sum_eq_one hx, one_mul]
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hAsum (t : Finset D) :
      A (fun x => ∑ i ∈ t, ψ i x) = fun x => ∑ i ∈ t, A (ψ i) x := by
    induction t using Finset.induction_on with
    | empty =>
      funext x
      simp only [Finset.sum_empty]
      exact hzero _ contDiff_const x (by simp)
    | @insert i t hit ih =>
      simp only [Finset.sum_insert hit]
      rw [hadd _ _ (hψ i) (ContDiff.sum (fun j _ => hψ j)), ih]
  have hi (i : D) : Integrable (A (ψ i)) μ ∧ (∫ x, A (ψ i) x ∂μ) ≤ 0 := by
    obtain ⟨hii, hineq⟩ := hUtest i (ψ i) (hψ i) (hψc i) (hψU i) (hψ0 i)
    have hsupport : Function.support (A (ψ i)) ⊆ U i := by
      intro x hx
      by_contra hxU
      exact hx (hzero _ (hψ i) x (fun h => hxU (hψU i h)))
    have hz : ∀ x ∉ U i, A (ψ i) x = 0 :=
      fun x hx => hzero _ (hψ i) x (fun h => hx (hψU i h))
    exact ⟨(integrableOn_iff_integrable_of_support_subset hsupport).mp hii,
      (setIntegral_eq_integral_of_forall_compl_eq_zero hz) ▸ hineq⟩
  have hglobal : Integrable (A φ) μ := by
    rw [← hsum, hAsum]
    exact integrable_finsetSum s (fun i _ => (hi i).1)
  refine ⟨hglobal.integrableOn, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hzero φ hφ x (fun h => hx (hφD h))), ← hsum, hAsum,
    integral_finsetSum s (fun i _ => (hi i).1)]
  exact Finset.sum_nonpos (fun i _ => (hi i).2)

end Poincare.Analysis
