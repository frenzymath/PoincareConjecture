import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Barriers
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Perturbation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Bounds.Quadratic











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle
open scoped BigOperators

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {O : M}



lemma SmoothExhaustion.exists_compact_quadratic_perturbation_pos_on
    (S : SmoothExhaustion F O) (V : Set M)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r ∧ x ∈ V})
    {C ε δ A T : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hδ : 0 < δ) (hA : 0 ≤ A) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ V ∧ ∀ t ∈ Ioc 0 T, ∀ x ∈ V, x ∉ K →
      ∀ q u w : ℝ, -C * w ^ 2 - C * u * w ≤ q → u ≠ 0 ∨ w ≠ 0 →
        0 < q + (ε * Real.exp (A * t) * S.toFun x / t) * w ^ 2 +
          (δ * Real.exp (A * t)) * u ^ 2 := by
  let B := C + C ^ 2 / (2 * δ) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨{x | S.toFun x ≤ T * B / ε ∧ x ∈ V}, hproper _, fun _ hx => hx.2, ?_⟩
  intro t ht x hxV hx q u w hlower hnonzero
  have hx' : T * B < S.toFun x * ε :=
    (div_lt_iff₀ hε).mp (lt_of_not_ge (fun h => hx ⟨h, hxV⟩))
  have he : 1 ≤ Real.exp (A * t) := Real.one_le_exp (mul_nonneg hA ht.1.le)
  have hscale : S.toFun x * ε ≤ ε * Real.exp (A * t) * S.toFun x := by
    have hh : 0 ≤ S.toFun x := (le_of_lt zero_lt_one).trans (S.one_le x)
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he hε.le) hh]
  have hα : B < ε * Real.exp (A * t) * S.toFun x / t :=
    (lt_div_iff₀ ht.1).mpr
      ((by nlinarith only [mul_le_mul_of_nonneg_right ht.2 hB.le] : B * t ≤ T * B)
        |>.trans_lt (hx'.trans_le hscale))
  have hp := Poincare.RicciFlow.Harnack.quadratic_perturbation_pos hδ
    (show C + C ^ 2 / (2 * δ) < ε * Real.exp (A * t) * S.toFun x / t by
      dsimp [B] at hα
      linarith only [hα]) hlower hnonzero
  have hψ : δ ≤ δ * Real.exp (A * t) := by nlinarith only [he, hδ]
  have hψu := mul_le_mul_of_nonneg_right hψ (sq_nonneg u)
  linarith only [hp, hψu]



lemma SmoothExhaustion.exists_compact_quadratic_perturbation_pos
    (S : SmoothExhaustion F O)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r})
    {C ε δ A T : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hδ : 0 < δ) (hA : 0 ≤ A) :
    ∃ K : Set M, IsCompact K ∧ ∀ t ∈ Ioc 0 T, ∀ x ∉ K,
      ∀ q u w : ℝ, -C * w ^ 2 - C * u * w ≤ q → u ≠ 0 ∨ w ≠ 0 →
        0 < q + (ε * Real.exp (A * t) * S.toFun x / t) * w ^ 2 +
          (δ * Real.exp (A * t)) * u ^ 2 := by
  obtain ⟨K, hK, _, hpos⟩ := S.exists_compact_quadratic_perturbation_pos_on univ
    (fun r => by simpa only [mem_univ, and_true] using hproper r) hC hε hδ hA (T := T)
  exact ⟨K, hK, fun t ht x hx => hpos t ht x (mem_univ x) hx⟩



lemma SmoothExhaustion.exists_initial_time_quadratic_perturbation_pos
    (S : SmoothExhaustion F O)
    {C ε δ A : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hδ : 0 < δ) (hA : 0 ≤ A) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t ∈ Ioc 0 t₀, ∀ x,
      ∀ q u w : ℝ, -C * w ^ 2 - C * u * w ≤ q → u ≠ 0 ∨ w ≠ 0 →
        0 < q + (ε * Real.exp (A * t) * S.toFun x / t) * w ^ 2 +
          (δ * Real.exp (A * t)) * u ^ 2 := by
  obtain ⟨t₀, ht₀, hpos⟩ :=
    Poincare.RicciFlow.Harnack.exists_initial_time_quadratic_perturbation_pos hC hε hδ
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht x q u w hlower hnonzero
  apply hpos t ht q u w _ _ hlower hnonzero
  · exact div_le_div_of_nonneg_right (S.le_exp_mul hε.le hA ht.1.le x) ht.1.le
  · have he := Real.one_le_exp (mul_nonneg hA ht.1.le)
    nlinarith only [he, hδ]

end PoincareConjecture.RicciFlow

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {O : M}



theorem exists_compact_hamilton_perturbation_pos
    (hC : RicciFlowCurvatureTheory.{u}) (S : RicciFlow.SmoothExhaustion F O)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r})
    {K ε δ A T : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Ioc 0 T, ∀ x, ∀ j ≤ 2,
      (F.connection t).curvatureDerivativeNorm j x ≤ K)
    (hcurv : ∀ t ∈ Ioc 0 T, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hε : 0 < ε) (hδ : 0 < δ) (hA : 0 ≤ A) :
    ∃ L : Set M, IsCompact L ∧ ∀ t ∈ Ioc 0 T, ∀ x ∉ L,
      ∀ (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
        (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ),
      (∀ i j, U i j = -U j i) →
      (Real.sqrt (∑ i, ∑ j, (U i j) ^ 2) ≠ 0 ∨
        Real.sqrt (∑ i, (W i) ^ 2) ≠ 0) →
      let b := (F.metric t).orthonormalBasis x
      0 < (∑ i, ∑ j, hamiltonM (F.connection t) t x (b i) (b j) * W i * W j) +
        2 * (∑ i, ∑ j, ∑ k, hamiltonP (F.connection t) x (b i) (b j) (b k) *
          U i j * W k) +
        (∑ i, ∑ j, ∑ k, ∑ l, (F.connection t).curvatureTensor x
          (b i) (b j) (b k) (b l) * U i j * U k l) +
        (ε * Real.exp (A * t) * S.toFun x / t) * (∑ i, (W i) ^ 2) +
        (δ * Real.exp (A * t)) * (∑ i, ∑ j, (U i j) ^ 2) := by
  let C := 6 * (n : ℝ) ^ 4 * K + 3 * (n : ℝ) ^ 5 * K ^ 2
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨L, hL, hpos⟩ := S.exists_compact_quadratic_perturbation_pos
    hproper hCnonneg hε hδ hA (T := T)
  refine ⟨L, hL, ?_⟩
  intro t ht x hx U W hU hn
  have hlower := hamilton_quadratic_lower_bound_of_bound (F.connection t)
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) ht.1.le x
    (hcurv t ht x) (hbound t ht x) U W hU
  have h := hpos t ht x hx _ _ _ hlower hn
  simpa only [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (W i))),
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => sq_nonneg (U i j))))] using h

end Poincare.RicciFlow.Harnack
